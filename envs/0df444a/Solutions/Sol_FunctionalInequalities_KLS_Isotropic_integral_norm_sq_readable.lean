-- Prove2me | solution 1 for FunctionalInequalities.KLS.Isotropic.integral_norm_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:46.020992+00:00
-- url     : https://prove2.me/submissions/87c1a3f8-aec8-4811-a98f-cf35db90819e

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
section Moments
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- For an isotropic law the raw second moments are `∫ ⟪u, x⟫ ⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.Isotropic.integral_inner_mul_inner
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ProbabilityMeasure E}
    (hν : Isotropic ν) (u v : E) :
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) = ⟪u, v⟫ := by
  calc
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) =
        ∫ x, ⟪u, x - ∫ y, id y ∂(ν : Measure E)⟫ *
          ⟪v, x - ∫ y, id y ∂(ν : Measure E)⟫ ∂(ν : Measure E) := by
      simp [hν.mean_zero]
    _ = ProbabilityTheory.covarianceBilin (ν : Measure E) u v := by
      rw [ProbabilityTheory.covarianceBilin_apply hν.memLp_two]
    _ = ⟪u, v⟫ := by
      rw [← Covariance.operator_inner, hν.covariance_identity]
      simp
end Moments
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open scoped RealInnerProductSpace in
/-- An isotropic law on `ℝⁿ` has `∫‖x‖² = n` (sum of the unit coordinate variances). -/
theorem solution {n : ℕ}
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hiso : FunctionalInequalities.KLS.Isotropic ν) :
    (∫ x, ‖x‖ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) = (n : ℝ) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hcoord (j : Fin n) : (∫ x, (x j) ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) = 1 := by
    have h := hiso.integral_inner_mul_inner (e j) (e j)
    rw [real_inner_self_eq_norm_sq, e.norm_eq_one, one_pow] at h
    simpa only [e, EuclideanSpace.basisFun_inner, ← pow_two] using h
  have hints (j : Fin n) : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x j) ^ 2)
      (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh : MemLp (fun x => ⟪e j, x⟫) 2 (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [Function.comp_def, id_eq, innerSL_apply_apply] using
        (innerSL ℝ (e j)).comp_memLp' hiso.memLp_two
    simpa only [e, EuclideanSpace.basisFun_inner] using hh.integrable_sq
  calc
    (∫ x, ‖x‖ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) = ∫ x, ∑ j : Fin n, (x j) ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
      congr 1
      funext x
      exact EuclideanSpace.real_norm_sq_eq x
    _ = ∑ j : Fin n, ∫ x, (x j) ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) :=
      integral_finsetSum _ (fun j _ => hints j)
    _ = (n : ℝ) := by simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
