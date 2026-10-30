-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_true_exp_clock_nonnegative_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:56:05.905535+00:00
-- url     : https://prove2.me/submissions/a0f567e9-c4fa-4f32-80a9-5ac13612a2b5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The actual real exponential observation clock is nonnegative almost
everywhere, directly from its Proved exact positive-tail probability. -/
theorem solution
    (p : ℝ) (hp : 0 < p) :
    ∀ᵐ r : ℝ ∂(expMeasure p), 0 ≤ r := by
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  have htail : expMeasure p (Ioi (0 : ℝ)) = 1 := by
    simpa only [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one] using
      avram_ws01e_b_expMeasure_strict_survival_real p 0 hp le_rfl
  have hnonpos : expMeasure p (Iic (0 : ℝ)) = 0 := by
    rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, htail]
    simp
  apply (ae_iff).2
  have hsub : {r : ℝ | ¬ 0 ≤ r} ⊆ Iic (0 : ℝ) := by
    intro r hr
    exact le_of_lt (lt_of_not_ge hr)
  exact measure_mono_null hsub hnonpos
