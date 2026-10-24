-- Prove2me | solution 1 for FunctionalInequalities.exists_norm_sq_eq_inner_of_isSymmetric_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:50:25.286989+00:00
-- url     : https://prove2.me/submissions/74634614-5b53-4596-99aa-7e1595765a23

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities in
/-- A symmetric operator with nonnegative quadratic form has a continuous linear norm factor satisfying `⟪T v, v⟫ = ‖B v‖²`. -/
theorem solution (T : V →L[ℝ] V)
    (hT : T.toLinearMap.IsSymmetric) (hpos : ∀ v, 0 ≤ inner ℝ (T v) v) :
    ∃ B : V →L[ℝ] V, ∀ v, inner ℝ (T v) v = ‖B v‖ ^ 2 := by
  set e := hT.eigenvectorBasis rfl with he
  set lam := hT.eigenvalues rfl with hlam
  have hTe : ∀ i, T (e i) = lam i • e i := fun i ↦ hT.apply_eigenvectorBasis rfl i
  have hlam_nonneg : ∀ i, 0 ≤ lam i := by
    intro i
    have h2 := hpos (e i)
    rw [hTe i, real_inner_smul_left, real_inner_self_eq_norm_sq, e.orthonormal.1 i] at h2
    simpa using h2
  -- `B v = ∑ i, √(lam i) * ⟪e i, v⟫ • e i`
  let B : V →L[ℝ] V := ∑ i, Real.sqrt (lam i) • (innerSL ℝ (e i)).smulRight (e i)
  refine ⟨B, fun v ↦ ?_⟩
  have hB : B v = ∑ i, (Real.sqrt (lam i) * inner ℝ (e i) v) • e i := by
    simp only [B, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul]
    rfl
  -- `T v = ∑ i, lam i * ⟪e i, v⟫ • e i`
  have hTv : T v = ∑ i, (lam i * inner ℝ (e i) v) • e i := by
    conv_lhs => rw [← e.sum_repr' v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, hTe i, smul_smul, mul_comm]
  have hinner : inner ℝ (T v) v = ∑ i, lam i * inner ℝ (e i) v ^ 2 := by
    rw [hTv, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_smul_left, sq, mul_assoc]
  have hnorm : ‖B v‖ ^ 2 = ∑ i, (Real.sqrt (lam i) * inner ℝ (e i) v) ^ 2 := by
    rw [hB, ← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_smul_left, e.orthonormal.inner_right_fintype, sq]
  rw [hinner, hnorm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_pow, Real.sq_sqrt (hlam_nonneg i)]
