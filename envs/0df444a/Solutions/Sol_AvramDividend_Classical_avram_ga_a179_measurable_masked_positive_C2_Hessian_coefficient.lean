-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a179_measurable_masked_positive_C2_Hessian_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:41:14.533801+00:00
-- url     : https://prove2.me/submissions/31f6c308-7070-4d45-9e39-cb3d938e25ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a161_original_positive_C2_gaussian_stopped_iterated_derivative_ae_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-- A finite stopped-source Hessian coefficient is a.e. strongly measurable:
replace inactive or non-positive arguments by one, then mask after applying
the already Proved C2 derivative measurability lemma. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 2 w (Ioi (0 : ℝ)))
    (A : Ω → Prop) [DecidablePred A]
    (hA : MeasurableSet {ω : Ω | A ω})
    (Y : Ω → ℝ) (hY : Measurable Y)
    (hPos : ∀ᵐ ω ∂P, A ω → 0 < Y ω)
    (E : ℝ) :
    AEStronglyMeasurable (fun ω =>
      if A ω then E * iteratedDeriv 2 w (Y ω) else 0) P := by
  let V : Ω → ℝ := fun ω => if A ω then Y ω else 1
  have hVm : Measurable V := Measurable.ite hA hY measurable_const
  have hVp : ∀ᵐ ω ∂P, 0 < V ω := by
    filter_upwards [hPos] with ω hp
    by_cases ha : A ω
    · simpa only [V, if_pos ha] using hp ha
    · simp only [V, if_neg ha]
      norm_num
  have hJet := avram_ga_a161_original_positive_C2_gaussian_stopped_iterated_derivative_ae_measurable
    P w hw 2 (by norm_num) V hVm hVp
  have hm : AEStronglyMeasurable
      (fun ω => if A ω then E * iteratedDeriv 2 w (V ω) else 0) P := by
    have hi : AEStronglyMeasurable
        (Set.indicator {ω : Ω | A ω}
          (fun ω => E * iteratedDeriv 2 w (V ω))) P :=
      (hJet.const_mul E).indicator hA
    apply hi.congr
    filter_upwards [] with ω
    by_cases ha : A ω <;> simp [Set.indicator,ha]
  exact hm.congr (Filter.Eventually.of_forall (fun ω => by
    by_cases ha : A ω <;> simp [V, ha]))
