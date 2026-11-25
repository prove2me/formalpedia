-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.CosetIndexLemmas.round_window_eventual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:10:27.985916+00:00
-- url     : https://prove2.me/submissions/d013e567-d7e9-4396-9ae6-0d36f9e4057a

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBracketBoundOfSizeWindows
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf
import Theorems.Thm_Formalism_LFunctionChainParameters_CosetIndexLemmas_ev_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.CosetIndexLemmas
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost
open Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.CosetIndexLemmas
theorem _root_.solution : RoundWindowEv := by
  intro ε c hε hc
  obtain ⟨x1, hx1, h1⟩ := ev_exp c ((1 : ℝ) / 2 + ε / 2 + ε) 1 (ε / 3) one_pos (by positivity)
  refine ⟨x1, fun x m n hx hm hn => ?_⟩
  have hxa := h1 x hx
  have hx1' : 1 ≤ x := le_trans hx1 hx
  have hx0 : 0 < x := by linarith
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
  have hX : XppTx x ε n = x * n * Real.exp (x ^ (ε / 3)) := by
    unfold XppTx wppTx bpTx aTx XpTx bTx
    have := Real.exp_pos (x ^ ε)
    have := Real.exp_pos (x ^ (ε / 3))
    have hn0 : 0 < n := by linarith
    field_simp
  rw [hX]
  have hE : 0 < Real.exp (x ^ (ε / 3)) := Real.exp_pos _
  rw [one_mul] at hxa
  calc c * m * x ^ ε ≤ c * x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε := by gcongr
    _ = c * x ^ ((1 : ℝ) / 2 + ε / 2 + ε) := by rw [mul_assoc, ← Real.rpow_add hx0]
    _ ≤ Real.exp (x ^ (ε / 3)) := hxa
    _ ≤ x * n * Real.exp (x ^ (ε / 3)) := by
        have : 1 ≤ x * n := by nlinarith
        nlinarith
end Formalism.LFunctionChainParameters.CosetIndexLemmas
