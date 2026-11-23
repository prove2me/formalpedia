-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.Lam_latZ_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:01.450684+00:00
-- url     : https://prove2.me/submissions/c14e02e6-8398-447a-b620-5199d31d19cc

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_mulVec_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_lower_right_block_is_diagonal
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x9_Lam_mul__36cdfb417c73
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mat_det_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mat_Lam_mulVec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (x : Fin n → R) (hx : x ∈ latZ R (Z₀ * p)) : ∀ j, abelian₂ R k Z₀ x j ∈ R := by
  obtain ⟨t, e⟩ := (mem_latZ R _ x).1 hx
  rw [Lam_mul' R k Z₀ p hp, mat_Lam_mulVec R k _ (mat_det_mul R k Z₀ p hd hp) x t e]
  refine isD_mulVec_int R k (lower_right_block_is_diagonal R k hp.1) fun j => ?_
  simp only [msk]
  split_ifs
  · rw [coeLin_apply]; exact (t j).2
  · exact R.zero_mem
end Formalism.FourierDecayAlt.P.A5x9
