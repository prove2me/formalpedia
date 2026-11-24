-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.joint_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:25.341481+00:00
-- url     : https://prove2.me/submissions/65186977-530c-43d8-a615-b0e05efc58c0

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_error_sizes

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
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
namespace Formalism.LFunctionChainParameters.LErr
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] :
    LeadingTermGrowthJoint (H := H) := by
  intro hTop W _ _ Top _ m f Dd C Xpp eK K D N ell TT T2 a w eT eP hSt hS hDIV hE hH hCount hSl hSlN
    hLo hSI hHH hF hW hX hB0 hNc i1 i2 i3 i4 i5
  have h103 := hSt ⟨0⟩ hS hDIV hE hH hCount hSl hSlN hLo hSI hHH hF
  have hErr := error_sizes Dd C Xpp eK K hW hX
  have hx : 1 ≤ Dd.x := hW.1.1
  have hnT : Dd.nT = (TT.card : ℝ) := by
    unfold Data.nT
    rw [Fintype.card_congr eT, Fintype.card_coe]
  have hbr : ErrText Dd
      ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold ErrText errorBracketSizeWindows
    rw [hnT]
    gcongr
  refine hTop Dd D N ell TT a w eT eP _ i1 i2 i3 i4 i5 ?_
  have hp : 0 ≤ Dd.x ^ (CErr C * Dd.ε) := Real.rpow_nonneg (by linarith) _
  have := mul_le_mul_of_nonneg_left hbr hp
  linarith
end Formalism.LFunctionChainParameters.LErr
