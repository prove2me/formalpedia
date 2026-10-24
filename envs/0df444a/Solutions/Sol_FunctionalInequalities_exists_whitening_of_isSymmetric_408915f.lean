-- Prove2me | solution 1 for FunctionalInequalities.exists_whitening_of_isSymmetric_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:41:03.203988+00:00
-- url     : https://prove2.me/submissions/631c961b-fd53-4ef0-bc25-62afa574c377

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Topology.Algebra.Module.FiniteDimension

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
/-- A symmetric operator with positive definite quadratic form has a self-adjoint continuous linear
equivalence `W` with `⟪T (W u), W v⟫ = ⟪u, v⟫`. Positivity of `W` is not part of this conclusion. -/
theorem solution (T : V →L[ℝ] V)
    (hT : T.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ (T v) v) :
    ∃ W : V ≃L[ℝ] V, (W : V →L[ℝ] V).adjoint = W ∧
      ∀ u v, inner ℝ (T (W u)) (W v) = inner ℝ u v := by
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  set e := hT.eigenvectorBasis rfl with he
  set lam := hT.eigenvalues rfl with hlam
  have hTe : ∀ i, T (e i) = lam i • e i := fun i ↦ hT.apply_eigenvectorBasis rfl i
  have hlam_pos : ∀ i, 0 < lam i := by
    intro i
    have hne : e i ≠ 0 := by
      intro h0
      have := e.orthonormal.1 i
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have h2 := hpos (e i) hne
    rw [hTe i, real_inner_smul_left, real_inner_self_eq_norm_sq, e.orthonormal.1 i] at h2
    simpa using h2
  have hsqrt_pos : ∀ i, 0 < Real.sqrt (lam i) := fun i ↦ Real.sqrt_pos.mpr (hlam_pos i)
  -- `W₀ v = ∑ i, (√(lam i))⁻¹ * ⟪e i, v⟫ • e i`
  let W₀ : V →L[ℝ] V := ∑ i, (Real.sqrt (lam i))⁻¹ • (innerSL ℝ (e i)).smulRight (e i)
  have hW₀ : ∀ v, W₀ v = ∑ i, ((Real.sqrt (lam i))⁻¹ * inner ℝ (e i) v) • e i := by
    intro v
    simp only [W₀, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul]
    rfl
  have hcoef : ∀ i v, inner ℝ (e i) (W₀ v) = (Real.sqrt (lam i))⁻¹ * inner ℝ (e i) v := by
    intro i v
    rw [hW₀, e.orthonormal.inner_right_fintype]
  have hinj : Function.Injective W₀ := by
    intro u v huv
    have h : ∀ i, inner ℝ (e i) u = inner ℝ (e i) v := by
      intro i
      have := congrArg (fun w ↦ inner ℝ (e i) w) huv
      simp only [hcoef] at this
      exact mul_left_cancel₀ (inv_ne_zero (hsqrt_pos i).ne') this
    rw [← e.sum_repr' u, ← e.sum_repr' v]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [h i]
  let W : V ≃L[ℝ] V := (LinearEquiv.ofInjectiveEndo W₀.toLinearMap hinj).toContinuousLinearEquiv
  have hW : ∀ v, W v = W₀ v := fun v ↦ rfl
  have hsymm : ∀ u v, inner ℝ (W₀ u) v = inner ℝ u (W₀ v) := by
    intro u v
    rw [hW₀, hW₀, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_smul_left, real_inner_smul_right, ← real_inner_comm u (e i)]
    ring
  refine ⟨W, ?_, ?_⟩
  · symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    exact hsymm x y
  · intro u v
    rw [hW, hW, hW₀ u, map_sum, sum_inner]
    have hterm : ∀ i, inner ℝ (T (((Real.sqrt (lam i))⁻¹ * inner ℝ (e i) u) • e i)) (W₀ v) =
        inner ℝ (e i) u * inner ℝ (e i) v := by
      intro i
      rw [map_smul, hTe i, smul_smul, real_inner_smul_left, hcoef]
      have hs : (Real.sqrt (lam i))⁻¹ * (Real.sqrt (lam i))⁻¹ * lam i = 1 := by
        rw [← mul_inv, Real.mul_self_sqrt (hlam_pos i).le]
        exact inv_mul_cancel₀ (hlam_pos i).ne'
      calc _ = ((Real.sqrt (lam i))⁻¹ * (Real.sqrt (lam i))⁻¹ * lam i) *
            (inner ℝ (e i) u * inner ℝ (e i) v) := by ring
        _ = _ := by rw [hs, one_mul]
    simp_rw [hterm]
    rw [← e.sum_inner_mul_inner u v]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm u (e i)]
