-- Prove2me | solution 1 for Formalism.L2.Th1.G.phSum_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:57.073799+00:00
-- url     : https://prove2.me/submissions/70e62878-640a-4bd2-b15e-e82bb04cb093

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
theorem _root_.solution {n : Type} [Fintype n] (c : n → K) (f g : PowerSeries K) :
    phSum c (f + g) = phSum c f + phSum c g := by
  unfold phSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero
    (MvPowerSeries.constantCoeff_X i)), smul_add]
end Formalism.L2.Th1.G
