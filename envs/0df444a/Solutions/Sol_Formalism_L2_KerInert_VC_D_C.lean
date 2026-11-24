-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.D_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:28.459894+00:00
-- url     : https://prove2.me/submissions/03a4bd51-3b9f-4916-a719-d16afe6614d1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_KerInert_VC_C_eq_algebraMap

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
theorem _root_.solution (a : R) : D W (PowerSeries.C a) = 0 := by
  rw [C_eq_algebraMap, Derivation.map_algebraMap]
end Formalism.L2.KerInert.VC
