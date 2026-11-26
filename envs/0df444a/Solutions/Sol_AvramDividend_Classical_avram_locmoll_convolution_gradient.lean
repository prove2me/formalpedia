-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_convolution_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:20:57.502552+00:00
-- url     : https://prove2.me/submissions/9a3c0716-1549-4eda-98e9-759753bc39bc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_restricted_secant_convolution
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (V ρ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hVmono : Monotone V) (hVnonneg : ∀ y, 0 ≤ V y)
    (hVzero : ∀ y < 0, V y = 0)
    (hVsec : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u)
    (hρI : Integrable ρ) (hρnorm : (∫ r, ρ r) = 1)
    (hρpos : 0 ≤ᵐ[volume] ρ)
    (hρsupport : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hI : ∀ y : ℝ, Integrable (fun r => ρ r * V (y - r)))
    (hg : ContDiff ℝ 2 (fun y => ∫ r, ρ r * V (y - r))) :
    let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
    ∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y := by 
  dsimp only
  let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
  have hsec (a b : ℝ) (ha : 2 * (δ / 3) ≤ a) (hab : a ≤ b) :
      b - a ≤ g b - g a := by
    exact avram_locmoll_restricted_secant_convolution volume ρ V
      (δ / 3) a b b (by linarith) ha hab le_rfl hρI hρnorm hρpos
      hρsupport (fun u v hu huv _ => hVsec u v hu huv) (hI a) (hI b)
  have hgrad (y : ℝ) (hy : δ ≤ y) : 1 ≤ deriv g y := by
    let H : ℝ → ℝ := fun t => g (max t (2 * (δ / 3))) - max t (2 * (δ / 3))
    have hm : Monotone H := by
      intro a b hab
      have hs := hsec (max a (2 * (δ / 3))) (max b (2 * (δ / 3)))
        (le_max_right _ _) (max_le_max_right _ hab)
      change g (max a (2 * (δ / 3))) - max a (2 * (δ / 3)) ≤
        g (max b (2 * (δ / 3))) - max b (2 * (δ / 3))
      linarith
    have heq : H =ᶠ[𝓝 y] (g - id) := by
      filter_upwards [Ioi_mem_nhds (show 2 * (δ / 3) < y by linarith)]
        with t ht
      have ht' : 2 * (δ / 3) ≤ t := le_of_lt ht
      simp [H, max_eq_left ht']
    have hd : 0 ≤ deriv H y := hm.deriv_nonneg
    rw [heq.deriv_eq] at hd
    have hgdiff : DifferentiableAt ℝ g y :=
      (hg.differentiable (by norm_num)).differentiableAt
    rw [deriv_sub hgdiff differentiableAt_id, deriv_id] at hd
    linarith
  exact hgrad
