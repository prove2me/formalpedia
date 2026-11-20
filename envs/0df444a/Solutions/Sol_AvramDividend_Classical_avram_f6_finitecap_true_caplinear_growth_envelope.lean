-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_finitecap_true_caplinear_growth_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:36:06.622476+00:00
-- url     : https://prove2.me/submissions/0206c5a5-349b-4a3f-b074-e819a703cfd1

import Mathlib.Data.ENNReal.Real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (K : ℝ) (hbound : ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal → |w y| ≤ K)
    (z : ℝ) (hz : 0 ≤ z) :
    |if ENNReal.ofReal z ≤ C then w z
       else w C.toReal + (z - C.toReal)| ≤ K + z := by
  have heq : (ENNReal.ofReal z ≤ C) ↔ z ≤ C.toReal :=
    ENNReal.ofReal_le_iff_le_toReal hC
  by_cases hzc : z ≤ C.toReal
  · have hw := hbound z hz hzc
    simpa only [heq, hzc, if_pos] using
      (le_trans hw (le_add_of_nonneg_right hz))
  · have hlt : C.toReal < z := lt_of_not_ge hzc
    have hcap : |w C.toReal| ≤ K :=
      hbound C.toReal ENNReal.toReal_nonneg le_rfl
    have hright : |w C.toReal + (z - C.toReal)| ≤
        |w C.toReal| + |z - C.toReal| := abs_add_le _ _
    have hpositive : 0 ≤ z - C.toReal := sub_nonneg.mpr hlt.le
    rw [if_neg (fun hh => hzc (heq.mp hh))]
    rw [abs_of_nonneg hpositive] at hright
    have hCnonneg : 0 ≤ C.toReal := ENNReal.toReal_nonneg
    linarith
