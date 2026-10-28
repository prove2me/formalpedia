-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.sqrt_sum_sq_sum_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:32:50.247868+00:00
-- url     : https://prove2.me/submissions/cfedab32-7252-45fe-be0b-82cef8d24015

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section S4Section6Pointwise
variable {n : ℕ}
section Masks
/-- Minkowski / ℓ² triangle inequality for finite sums of squares. -/
theorem solution {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → ℝ) :
    Real.sqrt (∑ i, (∑ q ∈ s, f q i) ^ 2) ≤ ∑ q ∈ s, Real.sqrt (∑ i, f q i ^ 2) := by
  let x : κ → EuclideanSpace ℝ ι := fun q => WithLp.toLp 2 (f q)
  have hn : ∀ q, ‖x q‖ = Real.sqrt (∑ i, f q i ^ 2) := by
    intro q
    rw [EuclideanSpace.norm_eq]
    simp [x, Real.norm_eq_abs, sq_abs]
  have hs : ‖∑ q ∈ s, x q‖ = Real.sqrt (∑ i, (∑ q ∈ s, f q i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [x, Real.norm_eq_abs, sq_abs]
  calc Real.sqrt (∑ i, (∑ q ∈ s, f q i) ^ 2) = ‖∑ q ∈ s, x q‖ := hs.symm
    _ ≤ ∑ q ∈ s, ‖x q‖ := norm_sum_le s x
    _ = ∑ q ∈ s, Real.sqrt (∑ i, f q i ^ 2) := Finset.sum_congr rfl fun q _ => hn q
