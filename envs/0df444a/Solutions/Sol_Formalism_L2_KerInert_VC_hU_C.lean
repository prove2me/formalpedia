-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.hU_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:36.694603+00:00
-- url     : https://prove2.me/submissions/cd323d8d-64fc-4ddb-bb34-ac395da7d865

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one


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
theorem _root_.solution : PowerSeries.C (C.u : R) * PowerSeries.C ((C.u⁻¹ : Rˣ) : R) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]
end Formalism.L2.KerInert.VC
