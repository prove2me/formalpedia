-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.losses_of_setting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:30:49.935242+00:00
-- url     : https://prove2.me/submissions/dd2d724f-472a-4024-9a63-5ab84d6e1355

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : LeadingTermLossesOfWindow := by
  intro P ι κ τ U U0 Ω Ps s J TT io D o sel W Top _ m f Dd Cc hC hx hε hC0 dx dε db dT dm dA dG dI hc he
  obtain ⟨c1, c2⟩ := hC
  have hb : 0 < P.b := Real.exp_pos _
  have hU : 0 ≤ unitU P J.card TT.card := by unfold unitU; positivity
  have hy : 1 ≤ P.x ^ (Cc.eLoss * P.ε) := Real.one_le_rpow hx (mul_nonneg he hε)
  have hLo : Dd.LoP Cc = Cc.cLoss * unitU P J.card TT.card * P.x ^ (Cc.eLoss * P.ε) := by
    unfold Data.LoP Data.nT unitU
    rw [dx, dε, db, dT, dm]
    ring
  have hc0 : 0 ≤ Cc.cLoss := by linarith
  have h1 : (3 * P.C + 13) * unitU P J.card TT.card ≤ Dd.LoP Cc := by
    rw [hLo]
    calc (3 * P.C + 13) * unitU P J.card TT.card ≤ Cc.cLoss * unitU P J.card TT.card :=
          mul_le_mul_of_nonneg_right hc hU
      _ ≤ Cc.cLoss * unitU P J.card TT.card * P.x ^ (Cc.eLoss * P.ε) :=
          le_mul_of_one_le_right (mul_nonneg hc0 hU) hy
  have h2 : unitU P J.card TT.card ≤ (3 * P.C + 13) * unitU P J.card TT.card := by
    have : (1 : ℝ) ≤ 3 * P.C + 13 := by linarith
    exact le_mul_of_one_le_left hU this
  intro u0
  refine ⟨?_, ?_⟩
  · rw [dA, dG]; exact (c1 (sel u0)).trans h1
  · rw [dI]; exact (c2 (sel u0)).trans (h2.trans h1)
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
