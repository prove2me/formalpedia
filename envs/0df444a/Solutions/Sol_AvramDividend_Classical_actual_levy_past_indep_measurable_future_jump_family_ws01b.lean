-- Prove2me | solution 1 for AvramDividend.Classical.actual_levy_past_indep_measurable_future_jump_family_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:10:47.156155+00:00
-- url     : https://prove2.me/submissions/923c3ff1-b20a-4f3a-8b6f-48ad89270d54

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_deterministicTime_history_future_product_law

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal


theorem solution
    {Ω E F : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → E)
    (hH : Measurable[𝓕 s] H)
    (Fpath : (ℝ≥0 → ℝ) → F)
    (hF : Measurable Fpath) :
    IndepFun H
      (fun ω : Ω =>
        Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P := by
  have := X.isProbability
  have hXm : ∀ t, Measurable (X.X t) := fun t =>
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hHm : Measurable H := hH.mono (𝓕.le s) le_rfl
  have hY : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) :=
    measurable_pi_lambda _ (fun t => (hXm _).sub (hXm _))
  have hZ : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) :=
    measurable_pi_lambda _ (fun t => hXm t)
  have hlaw := levy_deterministicTime_history_future_product_law X s H hH
  have hmarg : Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) P =
      Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
    have h2 := congrArg (Measure.map Prod.snd) hlaw
    rw [Measure.map_map measurable_snd (hHm.prodMk hY), Measure.map_snd_prod] at h2
    rw [Measure.map_apply hHm MeasurableSet.univ, Set.preimage_univ, measure_univ, one_smul] at h2
    exact h2
  have hind : IndepFun H (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) P := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hHm.aemeasurable hY.aemeasurable, hlaw, hmarg]
  exact hind.comp measurable_id hF
