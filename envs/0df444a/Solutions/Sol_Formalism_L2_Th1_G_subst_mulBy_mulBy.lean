-- Prove2me | solution 1 for Formalism.L2.Th1.G.subst_mulBy_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:59.528303+00:00
-- url     : https://prove2.me/submissions/d17a6e7e-77aa-444f-b528-932e394d2d6d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_eq_subst_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_mulBy_eq_fmul


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
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.G
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (a b : K) :
    PowerSeries.subst (mulBy l linv a) (mulBy l linv b) = mulBy l linv (b * a) := by
  rw [← Pts.fmul_eq_subst_mulBy h b (Pts.constantCoeff_mulBy h a), Pts.mulBy_eq_fmul a,
    Pts.fmul_fmul h b a PowerSeries.constantCoeff_X, ← Pts.mulBy_eq_fmul]
end Formalism.L2.Th1.G
