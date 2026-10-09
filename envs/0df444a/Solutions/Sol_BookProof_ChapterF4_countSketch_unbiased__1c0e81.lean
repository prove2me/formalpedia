-- Prove2me | solution 1 for BookProof.ChapterF4.countSketch_unbiased
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:02:13.266254+00:00
-- url     : https://prove2.me/submissions/754f2cf4-80af-489a-a200-caf69f6537e5

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.countSketch_unbiased
import Mathlib
import Definitions.Def_ChapterF4
open MeasureTheory
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hash : α → κ) (s : α → Ω → ℝ) (x y : α → ℝ)
    (hint : ∀ c c', Integrable (fun ω => s c ω * s c' ω) μ)
    (hs : ∀ c c', ∫ ω, s c ω * s c' ω ∂μ = if c = c' then 1 else 0) :
    ∫ ω, (∑ h, countSketch hash s x ω h * countSketch hash s y ω h) ∂μ
      = ∑ c, x c * y c := by

  rw [ MeasureTheory.integral_finset_sum ];
  · -- Expand the product inside the integral.
    have h_expand : ∀ ω h,      (countSketch hash s x ω h) * (countSketch hash s y ω h) = ∑ c ∈
        Finset.univ.filter (fun c => hash c = h), ∑ c' ∈ Finset.univ.filter (fun c' => hash c' = h),
            (x c * y c') * (s c ω * s c' ω) := by
      exact fun ω h => by rw [ countSketch, countSketch, Finset.sum_mul ] ;        exact
                          Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ;        exact
                                                             Finset.sum_congr rfl fun _ _ =>
                                                                 by ring;
    simp only [h_expand];
    rw [ Finset.sum_congr rfl fun h _ => MeasureTheory.integral_finset_sum _ fun c _ => ?_ ];
    · rw [ Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun i hi =>
        MeasureTheory.integral_finset_sum _ fun j hj => ?_ ];
      · simp only [integral_const_mul, hs];
        simp [ Finset.sum_filter, Finset.sum_comm ];
      · exact MeasureTheory.Integrable.const_mul ( ‹∀ c c', Integrable ( fun ω => s c ω * s c' ω )
          μ› i j ) _;
    · exact MeasureTheory.integrable_finset_sum _ fun c' _ => MeasureTheory.Integrable.const_mul (
        ‹∀ c c', MeasureTheory.Integrable ( fun ω => s c ω * s c' ω ) μ› c c' ) _;
  · intro h _; simp only [countSketch] ;
    simp only [Finset.sum_mul _ _ _, Finset.mul_sum];
    refine MeasureTheory.integrable_finset_sum _ fun i hi =>
      MeasureTheory.integrable_finset_sum _ fun j hj => ?_;
    convert MeasureTheory.Integrable.const_mul ( MeasureTheory.Integrable.const_mul ( ‹∀ c c',
        MeasureTheory.Integrable ( fun ω => s c ω * s c' ω ) μ› i j ) ( x i ) ) ( y j ) using 2
    · rfl
    · ring
