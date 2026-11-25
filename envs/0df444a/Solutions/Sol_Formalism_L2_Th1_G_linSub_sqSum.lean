-- Prove2me | solution 1 for Formalism.L2.Th1.G.linSub_sqSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:28:15.986345+00:00
-- url     : https://prove2.me/submissions/5965026c-2d71-4fc7-a1e7-d71866b802fe

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Several
import Theorems.Thm_Formalism_L2_Th1_G_linSubHom_apply
import Theorems.Thm_Formalism_L2_Th1_G_linSub_C
import Theorems.Thm_Formalism_L2_Th1_G_linSub_X

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
theorem _root_.solution {n m : Type} [Fintype n] [Fintype m] (A : n → m → K) (c : n → K) :
    linSub A (sqSum c) =
      ∑ i, MvPowerSeries.C (c i) * (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x) ^ 2 := by
  unfold sqSum
  rw [← linSubHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, linSubHom_apply, linSubHom_apply, linSub_C, linSub_X]
end Formalism.L2.Th1.G
