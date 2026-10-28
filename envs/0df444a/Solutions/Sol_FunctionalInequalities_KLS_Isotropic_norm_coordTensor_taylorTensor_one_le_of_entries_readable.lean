-- Prove2me | solution 1 for FunctionalInequalities.KLS.Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:34.719587+00:00
-- url     : https://prove2.me/submissions/c151ab34-4f80-4e97-a652-3e53df71bbe8

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Reduction
import Theorems.Thm_FunctionalInequalities_L2_integral_sq_eq_affine_decomposition_readable

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
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
end
end
end

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace
/-- **The `d = 1` Taylor bound from isotropy** (Bessel): `‖T_1 f‖_HS ≤ ‖f‖_{L²(μ)}`, given the entry
formula of the coordinate array. -/
theorem solution {n : ℕ}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hiso : FunctionalInequalities.KLS.Isotropic μ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hentry : ∀ i : Fin 1 → Fin n,
      FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
          (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i =
        ∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ (i 0), x⟫ * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
        (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1)‖ ≤
      (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal := by
    have hdecomp :=
      FunctionalInequalities.L2.integral_sq_eq_affine_decomposition_readable
        (μ : Measure (EuclideanSpace ℝ (Fin n)))
        hiso.memLp_two hiso.mean_zero hiso.integral_inner_mul_inner hf
    have hnonneg :
        0 ≤
          ∫ x, (FunctionalInequalities.L2.affineOrthPart
            (μ : Measure (EuclideanSpace ℝ (Fin n))) f x) ^ 2
            ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_nonneg
      intro x
      exact sq_nonneg _
    have hbessel :
        ∑ j : Fin n,
            (∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x
              ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 ≤
          ∫ x, f x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
      nlinarith [
        sq_nonneg (∫ x, f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))),
        hnonneg
      ]
    have hnorm :
        (∫ x, f x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
          (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2 := by
      let G := hf.toLp f
      have hG : G =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin n)))] f :=
        hf.coeFn_toLp
      calc
        (∫ x, f x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
            ∫ x, (G x) ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
              apply integral_congr_ae
              filter_upwards [hG] with x hx
              rw [hx]
        _ = ∫ x, ⟪G x, G x⟫
            ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
              apply integral_congr_ae
              filter_upwards [] with x
              simp [Real.norm_eq_abs, sq_abs]
        _ = ⟪G, G⟫ := by
              rw [MeasureTheory.L2.inner_def]
        _ = ‖G‖ ^ 2 := by
              rw [real_inner_self_eq_norm_sq]
        _ = (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2 := by
              rw [Lp.norm_toLp]
    have hsum :
        ∑ i : Fin 1 → Fin n,
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i‖ ^ 2 =
          ∑ j : Fin n,
            (∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x
              ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 := by
      calc
        ∑ i : Fin 1 → Fin n,
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i‖ ^ 2 =
            ∑ i : Fin 1 → Fin n,
              (∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ (i 0), x⟫ * f x
                ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hentry i, Real.norm_eq_abs, sq_abs]
        _ = ∑ j : Fin n,
            (∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x
              ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 := by
              exact
                Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ _ (fun i => rfl)
    rw [EuclideanSpace.norm_eq]
    calc
      Real.sqrt
          (∑ i : Fin 1 → Fin n,
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i‖ ^ 2) ≤
          Real.sqrt
            ((eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2) := by
              apply Real.sqrt_le_sqrt
              calc
                ∑ i : Fin 1 → Fin n,
                    ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                        (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i‖ ^ 2 =
                    ∑ j : Fin n,
                      (∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x
                        ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 := hsum
                _ ≤ ∫ x, f x ^ 2
                    ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := hbessel
                _ = (eLpNorm f 2
                    (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2 := hnorm
      _ = (eLpNorm f 2
          (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal := by
        rw [Real.sqrt_sq (ENNReal.toReal_nonneg)]
