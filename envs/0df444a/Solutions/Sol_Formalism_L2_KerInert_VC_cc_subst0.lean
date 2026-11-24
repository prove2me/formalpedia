-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.cc_subst0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:41:28.881177+00:00
-- url     : https://prove2.me/submissions/72b5acd7-cd4c-4a0f-8894-ef598dbeaad4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange

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
variable {R : Type} [CommRing R]
namespace Formalism.L2.KerInert.VC
theorem _root_.solution {f a : R⟦X⟧} (ha : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    constantCoeff (f.subst a) = 0 :=
  constantCoeff_subst_eq_zero ha f hf
end Formalism.L2.KerInert.VC
