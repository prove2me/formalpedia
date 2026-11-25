-- Prove2me | solution 1 for Formalism.L2.Th1.G.linSub_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:30.808445+00:00
-- url     : https://prove2.me/submissions/00622007-c7a8-4668-be13-323694ccfdc1

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
theorem _root_.solution {n m : Type} [Finite n] [Fintype m] (A : n → m → K) (i : n) :
    linSub A (MvPowerSeries.X i) = ∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x :=
  MvPowerSeries.subst_X (hasSubst_lin A) i
end Formalism.L2.Th1.G
