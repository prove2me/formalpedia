-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.core_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:28.065994+00:00
-- url     : https://prove2.me/submissions/cd8e0223-1573-4afe-b221-ed55f24755b7

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
namespace Formalism.LFunctionChainParameters.LErr
theorem _root_.solution {nT a b b' k L La B0 Nc M sA lW lk lH dI et Xpp yD yL
    cDiv cE cH cCount cSlope cSl1 cLoss : ℝ}
    (hyD : 0 ≤ yD) (hyL : 0 ≤ yL)
    (hnT : 0 ≤ nT) (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hM : 0 ≤ M) (hk : 0 < k)
    (hL0 : 0 ≤ L) (hLa0 : 0 ≤ La) (hb' : 0 ≤ b') (hX0 : 0 ≤ Xpp)
    (hsA0 : 0 ≤ sA) (hB0 : 0 ≤ B0) (hNc : 0 ≤ Nc)
    (hlW : 0 ≤ lW) (hlk0 : 0 ≤ lk) (hlH0 : 0 ≤ lH) (hdI : 1 ≤ dI) (het : 0 ≤ et)
    (c1 : 0 ≤ cDiv) (c2 : 0 ≤ cE) (c3 : 0 ≤ cH) (c4 : 0 ≤ cCount) (c5 : 0 ≤ cSlope)
    (c6 : 0 ≤ cSl1) (c7 : 0 ≤ cLoss) :
    et ≤ sA * (cCount * (La + M ^ 2 * La / k))
      + (cDiv * nT * a * La + cDiv * M * (B0 + Nc) * yD)
      + M * cE * B0
      + cSlope * nT * a * La * (1 + M / k)
      + lW
      + cLoss * nT * M * b * yL
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1)
      + dI * (4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) + et) := by
  have r1 : 0 ≤ sA * (cCount * (La + M ^ 2 * La / k))
      + (cDiv * nT * a * La + cDiv * M * (B0 + Nc) * yD)
      + M * cE * B0
      + cSlope * nT * a * La * (1 + M / k)
      + lW
      + cLoss * nT * M * b * yL
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1) := by positivity
  have r2 : 0 ≤ 4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) := by positivity
  have r3 := le_mul_of_one_le_left (add_nonneg r2 het) hdI
  linarith only [r1, r2, r3]
end Formalism.LFunctionChainParameters.LErr
