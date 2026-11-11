-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compound_jumpCount_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:28:43.786985+00:00
-- url     : https://prove2.me/submissions/9f7edd00-964b-4e44-9935-b17d6e154928

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_levy_foundations_compoundPoissonJumpCountLaw
import Theorems.Thm_ProbabilityTheory_integrable_id_poissonMeasure
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- The original driver count has finite first moment at each positive horizon,
by measurable transport of the exact Poisson count law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (t : ℝ≥0) :
    Integrable (fun ω => (LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) : ℝ)) P := by
  let f : Ω → ℕ := fun ω => LevyFoundations.jumpCount
    (fun n => LevyFoundations.arrival τ n ω) (t : ℝ)
  have hf : Measurable f :=
    AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public
      τ hd.measurable_interarrival (t : ℝ)
  have hmap : P.map f = ProbabilityTheory.poissonMeasure ((1 : ℝ≥0) * t) := by
    simpa only [f] using
      (levy_foundations_compoundPoissonJumpCountLaw hd (by norm_num) t)
  have hg : AEStronglyMeasurable (fun n : ℕ => (n : ℝ)) (P.map f) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).aestronglyMeasurable
  have hPoisson : Integrable (fun n : ℕ => (n : ℝ)) (P.map f) := by
    rw [hmap]
    exact ProbabilityTheory.integrable_id_poissonMeasure ((1 : ℝ≥0) * t)
  have htransfer := (integrable_map_measure hg hf.aemeasurable).mp hPoisson
  simpa only [Function.comp_def, f] using htransfer
