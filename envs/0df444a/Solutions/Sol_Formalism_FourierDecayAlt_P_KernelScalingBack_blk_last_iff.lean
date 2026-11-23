-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.blk_last_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:19.669279+00:00
-- url     : https://prove2.me/submissions/d3aa8b7a-8953-4128-b964-5f8929bfea86

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_blk_append_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_blk_append_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_blk_lt
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (l : List ℕ) (s j : ℕ) (hj : j < (l ++ [s]).sum) :
    blk (l ++ [s]) j = l.length ↔ l.sum ≤ j := by
  have hsum : (l ++ [s]).sum = l.sum + s := by simp
  constructor
  · intro h
    by_contra hlt'
    have hlt := not_le.1 hlt'
    rw [A5x5.blk_append_lt l s j hlt] at h
    exact (A5x5.blk_lt l j hlt).ne h
  · intro h
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
    exact A5x5.blk_append_ge l s i (by omega)
end Formalism.FourierDecayAlt.P.KernelScalingBack
