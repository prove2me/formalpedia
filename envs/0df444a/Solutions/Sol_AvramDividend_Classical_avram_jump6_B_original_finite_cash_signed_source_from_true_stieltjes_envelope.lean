-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_finite_cash_signed_source_from_true_stieltjes_envelope
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:09:37.309779+00:00
-- url     : https://prove2.me/submissions/2f0c80a1-81c8-418d-9e62-b954ed02cccc

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {ι : Type*} (S : Finset ι) (D0 Wx Wpost : ℝ)
    (E H : ι → ℝ) (Cash Error : ℝ≥0∞)
    (hD0 : 0 ≤ D0)
    (hE : ∀ i ∈ S, 0 ≤ E i)
    (hH : ∀ i ∈ S, 0 ≤ H i)
    (hInitial : D0 + Wpost - Wx ≤ 0)
    (hErrorFinite : Error ≠ ⊤)
    (hCash : Cash ≤ ENNReal.ofReal D0 +
      (∑ i ∈ S, ENNReal.ofReal (E i) * ENNReal.ofReal (H i)) + Error) :
    Cash.toReal + (Wpost - Wx) - (∑ i ∈ S, E i * H i) ≤ Error.toReal := by
  have hsum : (∑ i ∈ S, ENNReal.ofReal (E i) * ENNReal.ofReal (H i)) =
      ENNReal.ofReal (∑ i ∈ S, E i * H i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (hE i hi) (hH i hi))]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [ENNReal.ofReal_mul (hE i hi)]
  have hS0 : 0 ≤ ∑ i ∈ S, E i * H i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hE i hi) (hH i hi))
  rw [hsum] at hCash
  have hfin : ENNReal.ofReal D0 + ENNReal.ofReal (∑ i ∈ S, E i * H i) + Error ≠ ⊤ := by
    simp [hErrorFinite]
  have h1 := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin hCash) hfin).mpr hCash
  rw [ENNReal.toReal_add (by simp) hErrorFinite, ENNReal.toReal_add (by simp) (by simp),
    ENNReal.toReal_ofReal hD0, ENNReal.toReal_ofReal hS0] at h1
  linarith
