-- Prove2me | solution 1 for CoherenceTracking.Dephasing.eq_36
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:28:39.891454+00:00
-- url     : https://prove2.me/submissions/1f29b11e-36f5-499b-91d2-e7c7009b5bc3

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

open CoherenceTracking.Dephasing


theorem solution (γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c) (ω : ℝ → Fin 3 → ℝ) (v : ℝ → BVec) (T : ℝ)
    (hv : SolvesBloch γ ω v T) (hcoh : ∀ t ∈ Set.Ico 0 T, v t 0 ^ 2 + v t 1 ^ 2 = c) :
    ∀ t ∈ Set.Ioo 0 T, v t 2 ≠ 0 ∧ HasDerivAt (fun s => v s 2) (-(γ * c) / v t 2) t := by
  intro t ht
  have hd := hv.2 t ht
  have hd0 := hasDerivAt_pi.mp hd 0
  have hd1 := hasDerivAt_pi.mp hd 1
  have hd2 := hasDerivAt_pi.mp hd 2
  have m0 : (blochMatrix γ (ω t)).mulVec (v t) 0 = -γ * v t 0 - ω t 0 * v t 1 - ω t 2 * v t 2 := by
    simp [blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
  have m1 : (blochMatrix γ (ω t)).mulVec (v t) 1 = ω t 0 * v t 0 - γ * v t 1 - ω t 1 * v t 2 := by
    simp [blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
  have m2 : (blochMatrix γ (ω t)).mulVec (v t) 2 = ω t 2 * v t 0 + ω t 1 * v t 1 := by
    simp [blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [m0] at hd0
  rw [m1] at hd1
  rw [m2] at hd2
  have hf := (hd0.mul hd0).add (hd1.mul hd1)
  have hev : (fun s => v s 0 * v s 0 + v s 1 * v s 1) =ᶠ[nhds t] (fun _ => c) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have := hcoh s ⟨hs.1.le, hs.2⟩
    linarith [this]
  have hc0 : HasDerivAt (fun s => v s 0 * v s 0 + v s 1 * v s 1) 0 t :=
    (hasDerivAt_const t c).congr_of_eventuallyEq hev
  have heq := hf.unique hc0
  have hct := hcoh t ⟨ht.1.le, ht.2⟩
  have key : v t 2 * (ω t 2 * v t 0 + ω t 1 * v t 1) = -(γ * c) := by
    rw [← hct]; linarith
  have hne : v t 2 ≠ 0 := by
    intro h; rw [h, zero_mul] at key
    have : 0 < γ * c := mul_pos hγ hc
    linarith
  refine ⟨hne, ?_⟩
  have hv' : -(γ * c) / v t 2 = ω t 2 * v t 0 + ω t 1 * v t 1 := by
    rw [div_eq_iff hne, ← key]; ring
  rw [hv']
  exact hd2
