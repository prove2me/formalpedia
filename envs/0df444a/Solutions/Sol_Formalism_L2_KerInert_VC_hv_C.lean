-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.hv_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:18.006016+00:00
-- url     : https://prove2.me/submissions/4eed09f7-417c-462e-aafc-308e0b309f83

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_KerInert_VC_den_mul_vv
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.KerInert Formalism.L2.KerInert.VC
open Formalism.L2.Th1.A
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution : vv W C * (1 + PowerSeries.C C.s * X + (PowerSeries.C C.t - PowerSeries.C C.s * PowerSeries.C C.r) * wSer W) = 1 := by
  rw [mul_comm, ← map_mul, ← map_sub]; exact den_mul_vv W C
end Formalism.L2.KerInert.VC
