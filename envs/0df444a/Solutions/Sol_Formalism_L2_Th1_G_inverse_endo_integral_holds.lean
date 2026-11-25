-- Prove2me | solution 1 for Formalism.L2.Th1.G.inverse_endo_integral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:12:53.432088+00:00
-- url     : https://prove2.me/submissions/bcd52aa8-37a3-408a-a09d-38a5dafdabf6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Theorems.Thm_Formalism_L2_Th1_G_coeff_one_mulBy
import Theorems.Thm_Formalism_L2_Th1_G_subst_mulBy_mulBy
import Theorems.Thm_Formalism_L2_Th1_G_mulBy_one
import Theorems.Thm_Formalism_L2_Th1_G_intPS_of_left_inverse
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_mulBy


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
namespace Formalism.L2.Th1.G
theorem _root_.solution : InvEndInt := by
  intro K _ R l linv a h ha hai hE
  refine intPS_of_left_inverse R hE (Pts.constantCoeff_mulBy h a) ?_ ?_ ?_
  · rwa [coeff_one_mulBy h a]
  · rwa [coeff_one_mulBy h a]
  · rw [subst_mulBy_mulBy h, inv_mul_cancel₀ ha, mulBy_one h]
end Formalism.L2.Th1.G
