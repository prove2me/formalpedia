-- Prove2me | solution 1 for Formalism.L2.Th1.G.cc_toZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:13:19.307536+00:00
-- url     : https://prove2.me/submissions/4a76b1d6-58b6-438e-a0e9-2500adb32582

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Several

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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.G
theorem _root_.solution {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) {f : MvPowerSeries n K}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (toZ linv f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_zPt h0) (fun i => cc_zPt h0 i) hf
end Formalism.L2.Th1.G
