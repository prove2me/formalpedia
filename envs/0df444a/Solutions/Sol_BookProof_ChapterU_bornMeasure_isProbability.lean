-- Prove2me | solution 1 for BookProof.ChapterU.bornMeasure_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:35:10.816798+00:00
-- url     : https://prove2.me/submissions/898a3f2e-e468-4dab-aa4a-a3a771025eb5

-- Generated from ChapterU.lean — solution of BookProof.ChapterU.bornMeasure_isProbability
import Mathlib
import Definitions.Def_ChapterU
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterU



open MeasureTheory
open scoped ENNReal ProbabilityTheory TensorProduct

variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
theorem solution (Ψ : X → ℂ) (μ : Measure X)
    (hΨ : MemLp Ψ 2 μ) (hnorm : ∫ x, ‖Ψ x‖ ^ 2 ∂μ = 1) :
    IsProbabilityMeasure (bornMeasure Ψ μ) := by

  constructor;
  unfold bornMeasure;
  rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ] at hnorm;
  · rw [ ENNReal.toReal_eq_one_iff ] at hnorm ; aesop;
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
  · simpa using hΨ.1.norm.aemeasurable.pow_const 2 |> fun h => h.aestronglyMeasurable
