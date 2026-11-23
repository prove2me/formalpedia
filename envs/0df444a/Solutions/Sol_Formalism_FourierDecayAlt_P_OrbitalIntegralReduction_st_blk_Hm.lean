-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.st_blk_Hm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:22.100677+00:00
-- url     : https://prove2.me/submissions/27287f08-8b3f-4f15-80c5-20814b1a3ee7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_antidiagonal_block_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_eN_inl
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_eN_inr
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (m : ℕ) (t : Kˣ) (c : K) (ξ : Fin m → K)
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hu : IsUpUni u) :
    blkM (rfl : m + 1 = m + 1) (antidiagonalBlock m t) 0 (ξ ᵥ* antidiagonalBlock m t) c * u =
      (Hm (t : K) c ξ u).submatrix Fin.rev id := by
  ext i j
  rw [Matrix.mul_apply, ← Equiv.sum_comp (eN (rfl : m + 1 = m + 1)), Fintype.sum_sum_type]
  obtain ⟨i, rfl⟩ := (eN (rfl : m + 1 = m + 1)).surjective i
  rcases i with i | i
  · simp only [blkM_ll, blkM_lr, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single (Fin.rev i)]
    · rw [antidiagonal_block_apply, if_pos rfl, st_eN_inl, st_eN_inl]
      simp only [Matrix.submatrix_apply, id, Hm, Fin.rev_castSucc, Fin.cases_succ]
    · intro k _ hk
      rw [antidiagonal_block_apply, if_neg hk, zero_mul]
    · simp
  · simp only [blkM_rl, blkM_rr, Finset.univ_unique, Finset.sum_singleton]
    rw [st_eN_inr]
    simp only [Matrix.submatrix_apply, id, Hm, Fin.rev_last, Fin.cases_zero]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [st_eN_inl, Matrix.vecMul, dotProduct, Finset.sum_eq_single (Fin.rev k)]
      · rw [antidiagonal_block_apply, if_pos (Fin.rev_rev k).symm]; ring
      · intro l _ hl
        rw [antidiagonal_block_apply, if_neg, mul_zero]
        intro h2
        apply hl
        rw [h2, Fin.rev_rev]
      · simp
    · by_cases hj : j = Fin.last m
      · rw [if_pos hj, hj, hu.2, mul_one]
      · rw [if_neg hj, Formalism.DoubleCosetMeasures.P.Phase.up_zero hu (lt_of_le_of_ne (Fin.le_last j) hj), mul_zero]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
