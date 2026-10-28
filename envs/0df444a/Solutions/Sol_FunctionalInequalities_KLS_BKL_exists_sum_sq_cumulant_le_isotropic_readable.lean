-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.exists_sum_sq_cumulant_le_isotropic_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:32:23.16941+00:00
-- url     : https://prove2.me/submissions/e0677bcb-3705-48fd-8e40-55becff29afe

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Bound
import Theorems.Thm_FunctionalInequalities_KLS_BKL_exists_norm_cumulant_le_isotropic_readable

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ}
/-- A-priori energy bound in a fixed dimension. -/
theorem solution (d : ℕ) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      FunctionalInequalities.KLS.LogConcave ν → FunctionalInequalities.KLS.Isotropic ν → IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
        ∀ u : EuclideanSpace ℝ (Fin n),
          ∑ J : Fin d → Fin n, FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hbound⟩ := FunctionalInequalities.KLS.BKL.exists_norm_cumulant_le_isotropic_readable (n := n) (d + 1)
  refine ⟨(n : ℝ) ^ d * C ^ 2, by positivity, ?_⟩
  intro ν hlc hiso hc u
  have hbasis (j : Fin n) : ‖EuclideanSpace.basisFun (Fin n) ℝ j‖ = 1 :=
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one j
  have hterm (J : Fin d → Fin n) :
      FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤
          C ^ 2 * ‖u‖ ^ 2 := by
    have hop := (FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)).le_opNorm
      (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))
    have habs :
        |FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
          (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))| ≤ C * ‖u‖ := by
      calc
        _ ≤ ‖FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)‖ * ‖u‖ := by
          simpa only [Real.norm_eq_abs, Fin.prod_univ_succ, Fin.cons_zero,
            Fin.cons_succ, hbasis, Finset.prod_const_one, mul_one] using hop
        _ ≤ C * ‖u‖ :=
          mul_le_mul_of_nonneg_right (hbound ν hlc hiso hc) (norm_nonneg u)
    have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (norm_nonneg u))).2 habs
    simpa only [sq_abs, mul_pow] using hsq
  calc
    _ ≤ ∑ _J : Fin d → Fin n, C ^ 2 * ‖u‖ ^ 2 :=
      Finset.sum_le_sum (fun J _ => hterm J)
    _ = ((n : ℝ) ^ d * C ^ 2) * ‖u‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      ring
