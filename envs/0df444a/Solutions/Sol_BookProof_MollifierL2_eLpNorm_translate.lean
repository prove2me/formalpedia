-- Prove2me | solution 1 for BookProof.MollifierL2.eLpNorm_translate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:05:15.712009+00:00
-- url     : https://prove2.me/submissions/594341c6-9b9b-4721-b2ee-cb166399e39d

-- Generated from ChapterMollifierL2.lean — solution of BookProof.MollifierL2.eLpNorm_translate
import Mathlib
import Definitions.Def_ChapterMollifierL2
open BookProof.MollifierL2




open MeasureTheory Filter ENNReal Pointwise
open scoped NNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option maxHeartbeats 1000000 in
theorem solution {p : ℝ≥0∞} {f : E → F} (hf : AEStronglyMeasurable f μ) (a : E) :
    eLpNorm (fun x => f (x - a)) p μ = eLpNorm f p μ := eLpNorm_comp_measurePreserving hf (measurePreserving_sub_right μ a)
