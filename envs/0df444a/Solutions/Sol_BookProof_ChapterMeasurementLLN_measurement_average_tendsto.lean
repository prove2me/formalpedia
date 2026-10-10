-- Prove2me | solution 1 for BookProof.ChapterMeasurementLLN.measurement_average_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:57:51.949959+00:00
-- url     : https://prove2.me/submissions/48cac4be-7305-4c24-bafc-e01cc2b393e4

-- Generated from ChapterMeasurementLLN.lean — solution of BookProof.ChapterMeasurementLLN.measurement_average_tendsto
import Mathlib
import Definitions.Def_ChapterMeasurementLLN
open BookProof.ChapterMeasurementLLN



open MeasureTheory ProbabilityTheory
open scoped ENNReal


variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {k : ℕ}

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {k : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M : ℕ → Ω → Fin k) (f : Fin k → ℝ)
    (hmeas : ∀ i, Measurable (M i))
    (hindep : Pairwise (fun i j => IndepFun (M i) (M j) μ))
    (hident : ∀ i, IdentDistrib (M i) (M 0) μ μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => (∑ i ∈ Finset.range n, f (M i ω)) / n)
      Filter.atTop (nhds (∫ ω, f (M 0 ω) ∂μ)) := by

  have hf : Measurable f := measurable_of_countable f
  -- Apply the strong law of large numbers to the sequence `Xᵢ = f ∘ Mᵢ`.
  refine ProbabilityTheory.strong_law_ae_real (fun i ω => f (M i ω)) ?_ ?_ ?_
  · -- `X₀ = f ∘ M₀` is bounded by `∑ x, |f x|`, hence integrable on a probability space.
    refine MeasureTheory.Integrable.mono' (integrable_const (∑ x : Fin k, |f x|)) ?_ ?_
    · exact (hf.comp (hmeas 0)).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun x => |f x|)
        (fun x _ => abs_nonneg _) (Finset.mem_univ (M 0 ω))
  · -- Pairwise independence transfers from `M` to `f ∘ M`.
    intro i j hij; exact (hindep hij).comp hf hf
  · -- Identical distribution transfers from `M` to `f ∘ M`.
    intro i; exact (hident i).comp hf
