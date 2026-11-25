-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.right_lowering_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:52:59.246146+00:00
-- url     : https://prove2.me/submissions/4188ab2f-8eec-4757-b3f8-773b37f67e03

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_Sup_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_sup_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_sup_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_rz_linear
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Qr.RZLin := by
  intro E _ _ k r i D hD c F hF g hg
  obtain ⟨L, hL⟩ := CapelliCoordinates.rz_linear hF hg
  have hs : ∀ a b, CapelliCoordinates.Sup k r i (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ)) :=
    fun a b => CapelliCoordinates.sup_single a b
  rw [hL _ (CapelliCoordinates.sup_sum _ _ fun a _ => CapelliCoordinates.sup_sum _ _ fun b _ => (hs a b).smul (c a b))]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hL _ (hs a b)]
  rfl
end Formalism.FourierDecayAlt.P
