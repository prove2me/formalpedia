-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.sum_hsNormSq_conjugatedNoiseOperator_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:38:44.803693+00:00
-- url     : https://prove2.me/submissions/19d8a4ac-188b-4b9e-9b4e-c94f06a6ef85

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Bound
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_stdMatrix_conjugatedNoiseOperator_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_sum_sq_conjugatedNoiseMatrix_mulVec_le_readable

noncomputable section
section S5E1BLyapunovBound
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
  FunctionalInequalities.Analysis.CoordinateTensor
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
set_option maxHeartbeats 1000000 in
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (hLC : FunctionalInequalities.KLS.LogConcave μ)
    (h8 : FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact 2 8) (p : FunctionalInequalities.KLS.BKL.Localization.Param n)
    (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) :
    ∑ k, FunctionalInequalities.Analysis.hsNormSq (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p k) ≤ 8 * n := by
  classical
  have hmatrix (k : Fin n) :
      FunctionalInequalities.Analysis.hsNormSq (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p k) =
        ∑ a, ∑ b, (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseMatrix μ hc p k a b) ^ 2 := by
    have h :=
      congrArg
        (fun M : Matrix (Fin n) (Fin n) ℝ => ∑ a, ∑ b, M a b ^ 2)
        (FunctionalInequalities.KLS.BKL.Localization.stdMatrix_conjugatedNoiseOperator_readable μ hc hiso p k)
    simpa [FunctionalInequalities.Analysis.hsNormSq, FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix, Matrix.of_apply] using h
  have hsingle (k a b : Fin n) :
      ∑ j, FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseMatrix μ hc p k a j *
          (Pi.single b (1 : ℝ) : Fin n → ℝ) j =
        FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseMatrix μ hc p k a b := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro j hj hne
      simp [hne]
    · intro hb
      exact (hb (Finset.mem_univ b)).elim
  have hcolumn (b : Fin n) :
      ∑ k, ∑ a, (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseMatrix μ hc p k a b) ^ 2 ≤ 8 := by
    have h :=
      FunctionalInequalities.KLS.BKL.Localization.sum_sq_conjugatedNoiseMatrix_mulVec_le_readable μ hc hiso hLC h8 p hSym hQ
        (Pi.single b (1 : ℝ))
    simp_rw [hsingle] at h
    simpa [Pi.single_apply] using h
  calc
    ∑ k, FunctionalInequalities.Analysis.hsNormSq (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p k) =
        ∑ k, ∑ a, ∑ b, (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseMatrix μ hc p k a b) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hmatrix k]
    _ = ∑ k, ∑ b, ∑ a, (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseMatrix μ hc p k a b) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ k, ∑ a, (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseMatrix μ hc p k a b) ^ 2 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ b, 8 := by
      apply Finset.sum_le_sum
      intro b hb
      exact hcolumn b
    _ = 8 * n := by
      simp
      ring
