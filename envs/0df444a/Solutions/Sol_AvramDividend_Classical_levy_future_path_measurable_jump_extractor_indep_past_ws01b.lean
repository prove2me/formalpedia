-- Prove2me | solution 1 for AvramDividend.Classical.levy_future_path_measurable_jump_extractor_indep_past_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:27:46.224044+00:00
-- url     : https://prove2.me/submissions/6af67cb2-df1b-4cb2-b34d-b65e9b092722

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_deterministicTime_history_future_product_law
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- A measurable functional of the actual future Lévy increment path
is independent of every measurable past-filtration statistic. -/
theorem solution
    {Ω E F : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (J : (ℝ≥0 → ℝ) → F) (hJ : Measurable J) :
    IndepFun H
      (fun ω => J (fun t : ℝ≥0 =>
        X.X (s + t) ω - X.X s ω)) P := by
  let Z : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (s + t) ω - X.X s ω
  have hHm : Measurable H :=
    hH.mono (𝓕.le s) le_rfl
  have hsStop :
      IsStoppingTime 𝓕
        (fun _ : Ω => (s : WithTop ℝ≥0)) := by
    exact MeasureTheory.isStoppingTime_const 𝓕 s
  have hZm : Measurable Z := by
    simpa only [Z] using
      levy_boundedStopping_stoppedFuturePath_measurable
        X (fun _ : Ω => s) hsStop s (by intro ω; exact le_rfl)
  have hprod :
      Measure.map (fun ω => (H ω, Z ω)) P =
        (Measure.map H P).prod (Measure.map Z P) := by
    have hp :=
      levy_deterministicTime_history_future_product_law X s H hH
    have hstation := levy_shiftedFuturePath_stationary_law X s
    simpa only [Z, hstation] using hp
  have hIndep : IndepFun H Z P :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hHm.aemeasurable hZm.aemeasurable).2 hprod
  simpa [Z, Function.comp_def] using
    hIndep.comp measurable_id hJ
