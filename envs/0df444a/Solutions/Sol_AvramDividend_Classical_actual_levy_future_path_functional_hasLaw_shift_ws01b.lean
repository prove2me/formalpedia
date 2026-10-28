-- Prove2me | solution 1 for AvramDividend.Classical.actual_levy_future_path_functional_hasLaw_shift_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:30:19.272427+00:00
-- url     : https://prove2.me/submissions/1b628a28-fd6a-4b62-8700-bbbe63c4b601

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Any measurable full-path mark/jump statistic has the same law when
computed from the future Lévy increment path after deterministic time s. -/
theorem solution
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (Fpath : (ℝ≥0 → ℝ) → E) (hF : Measurable Fpath)
    (η : Measure E)
    (h0 : HasLaw
      (fun ω : Ω => Fpath (fun t : ℝ≥0 => X.X t ω)) η P) :
    HasLaw
      (fun ω : Ω =>
        Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω))
      η P := by
  let Z : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (s + t) ω - X.X s ω
  let W : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hZm : Measurable Z := by
    exact measurable_pi_lambda _ fun t =>
      (X.adapted.measurable (i := s + t)).sub
        (X.adapted.measurable (i := s))
  have hWm : Measurable W := levy_wholePath_measurable X
  have hstationary : Measure.map Z P = Measure.map W P := by
    simpa only [Z, W] using levy_shiftedFuturePath_stationary_law X s
  have hmap := congrArg (Measure.map Fpath) hstationary
  have hmapZ : Measure.map Fpath (Measure.map Z P) =
      Measure.map (Fpath ∘ Z) P := Measure.map_map hF hZm
  have hmapW : Measure.map Fpath (Measure.map W P) =
      Measure.map (Fpath ∘ W) P := Measure.map_map hF hWm
  refine ⟨(hF.comp hZm).aemeasurable, ?_⟩
  change Measure.map (Fpath ∘ Z) P = η
  rw [hmapZ, hmapW] at hmap
  exact hmap.trans h0.map_eq
