-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBoundCompact_two_of_letwinCompact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:27:44.983826+00:00
-- url     : https://prove2.me/submissions/7ebd6d04-fd9e-43cd-9386-14588dc910d7

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_LocalThirdCumulant
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis_readable
import Theorems.Thm_FunctionalInequalities_KLS_BorelLogConcave_exists_integrable_exp_norm_readable

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

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **BKL Lemma 4.2 (source scope), conditional on the Letwin quadratic bound**: for every isotropic
log-concave law `μ` with `LetwinQuadraticBound μ`, `∑_{jk} κ₃(u, b_j, b_k)² ≤ 8‖u‖²` in any orthonormal
basis; the exponential radius comes from Borell. The noncompact input is supplied separately by
`KLS.LogConcave.letwinQuadraticBound` in positive dimension; this interface remains conditional. -/
theorem FunctionalInequalities.KLS.LogConcave.sum_sq_cumulant_three_le_of_letwin (μ : ProbabilityMeasure E) (hLC : KLS.LogConcave μ)
    (hiso : KLS.Isotropic μ) (hL : LetwinQuadraticBound (μ : Measure E))
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) (u : E) :
    ∑ j, ∑ k, cumulant (μ : Measure E) 3 ![u, b j, b k] ^ 2 ≤ 8 * ‖u‖ ^ 2 := by
  obtain ⟨r, hr, hexp⟩ := ((KLS.LogConcave.borel_iff μ).1 hLC).exists_integrable_exp_norm_readable
  apply Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis_readable (μ : Measure E) hr hexp ?_
    hiso.integral_inner_mul_inner hL b u
  intro v
  have h := (innerSL ℝ v).integral_comp_comm (hiso.memLp_two.integrable (by norm_num))
  simpa only [Function.comp_def, innerSL_apply_apply, id_eq, hiso.mean_zero, inner_zero_right] using h
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
/-- **Base case of the compact induction** (BKL Lemma 4.2 for compactly supported laws): the compact
Letwin bound gives `CumulantBoundCompact 2 8`. -/
theorem solution (h : FunctionalInequalities.KLS.LogConcave.Suspension.LetwinCompactBound) :
    FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact 2 8 := by
  classical
  intro n μ hiso hLC hcompact u
  cases n with
  | zero =>
    have hs : (∑ J : Fin 2 → Fin 0, FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure _) 3
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin 0) ℝ (J k)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro J _hJ
      exact Fin.elim0 (J 0)
    rw [hs]
    positivity
  | succ n =>
    let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
    have hbound := FunctionalInequalities.KLS.LogConcave.sum_sq_cumulant_three_le_of_letwin μ hLC hiso
      (h (n + 1) (Nat.succ_pos _) μ hLC hiso hcompact) b u
    have heq : (∑ J : Fin 2 → Fin (n + 1), FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure _) 3
        (Fin.cons u fun k => b (J k)) ^ 2) =
        ∑ j, ∑ k, FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure _) 3 ![u, b j, b k] ^ 2 := by
      have hreindex := (finTwoArrowEquiv (Fin (n + 1))).symm.sum_comp
        (fun J => FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure _) 3 (Fin.cons u fun k => b (J k)) ^ 2)
      calc
        _ = ∑ q : Fin (n + 1) × Fin (n + 1), FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure _) 3
            (Fin.cons u fun k => b (((finTwoArrowEquiv (Fin (n + 1))).symm q) k)) ^ 2 :=
          hreindex.symm
        _ = ∑ q : Fin (n + 1) × Fin (n + 1), FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure _) 3
            ![u, b q.1, b q.2] ^ 2 := by
          apply Finset.sum_congr rfl
          intro q _hq
          congr 2
          ext i
          fin_cases i <;> rfl
        _ = _ := Fintype.sum_prod_type _
    change (∑ J : Fin 2 → Fin (n + 1), FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure _) 3
      (Fin.cons u fun k => b (J k)) ^ 2) ≤ _
    rw [heq]
    exact hbound
