-- Prove2me | solution 1 for Formalism.L2.Th1.G.WeierstrassCurveSeries.rescale_neg_one_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:27:41.868697+00:00
-- url     : https://prove2.me/submissions/c3c77dcd-0c13-4001-b192-6083cb722e7a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_CurveFormalFirstLevelHolds

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
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
open Formalism.G (unitBall)
open Formalism.L2.Th1.G.WeierstrassCurveSeries
namespace Formalism.L2.Th1.G.WeierstrassCurveSeries
theorem _root_.solution {K : Type} [Field K] (e : PowerSeries K)
    (h : ∀ n : ℕ, Odd n → PowerSeries.coeff n e = 0) : PowerSeries.rescale (-1 : K) e = e := by
  ext n
  rw [PowerSeries.coeff_rescale]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, one_mul]
  · rw [h n hn, mul_zero]
end Formalism.L2.Th1.G.WeierstrassCurveSeries
