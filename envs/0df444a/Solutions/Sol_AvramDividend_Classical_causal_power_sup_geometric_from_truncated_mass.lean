-- Prove2me | solution 1 for AvramDividend.Classical.causal_power_sup_geometric_from_truncated_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:10:07.992143+00:00
-- url     : https://prove2.me/submissions/2d331b11-26c7-40fa-abd7-99506da963af

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Geometric convolution-power masses give uniform successor bounds. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (B ρ : ℝ)
    (hB : 0 ≤ B) (hκle : ∀ t : ℝ, κ t ≤ B)
    (hFnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFstep : ∀ n : ℕ, ∀ x : ℝ, F (n + 1) x =
      ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume)
    (hFprod : ∀ n : ℕ, ∀ x : ℝ,
      IntegrableOn (fun s : ℝ => κ (x - s) * F n s)
        (Ioc (0 : ℝ) x) volume)
    (hFi : ∀ n : ℕ, ∀ x : ℝ,
      IntegrableOn (F n) (Ioc (0 : ℝ) x) volume)
    (hFmass : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1)) :
    ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      F (n + 1) x ≤ B * ρ ^ (n + 1) := by
  intro n x hx
  rw [hFstep n x]
  calc
    (∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume) ≤
        ∫ s in Ioc (0 : ℝ) x, B * F n s ∂volume := by
      apply integral_mono_ae (hFprod n x) ((hFi n x).const_mul B)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_le_mul_of_nonneg_right (hκle (x - s))
        (hFnonneg n s (le_of_lt hs.1))
    _ = B * (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) := by
      rw [integral_const_mul]
    _ ≤ B * ρ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (hFmass n x hx) hB
