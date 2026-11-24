-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelEv.askDA_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:45:11.856433+00:00
-- url     : https://prove2.me/submissions/2709c59e-240f-4305-9373-7fcae4b27e5d

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_hostFacts_DA
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelEv_geo7

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.LChain.ModelEv
open Model
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LChain.ModelEv
theorem _root_.solution (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) (ha : 0 ≤ a) (hw : ∀ ρ, 0 ≤ w ρ) :
    ASK (DA (H := H)) N a t w ≤ a := by
  classical
  have hd : (((DA (H := H)).d : ℕ) : ℝ) = 7 := by
    show (((7 : ℕ) : ℕ) : ℝ) = 7
    norm_num
  have h2 : askD (DA (H := H)) N a t w ≤ a / 6 := by
    unfold askD
    rw [hd]
    refine le_trans (Finset.sum_le_sum (g := fun i => a / (7 : ℝ) ^ i) fun i _ => ?_) ?_
    · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := {(sgc0 : E0 × H)}) ?_
        (fun _ _ _ => le_max_right _ _)) ?_
      · intro g hg
        obtain ⟨-, hg1, hg2⟩ := Finset.mem_filter.1 hg
        have e : g - i • (DA (H := H)).frob (DA (H := H)).d = g := by
          show g - i • (0 : E0 × H) = g
          simp
        rw [e] at hg1
        rcases (hostFacts_DA.inertia_d g).1 hg1 with h | h
        · exact absurd (by rw [h]; simp [InPhi]) hg2
        · exact Finset.mem_singleton.2 h
      · rw [Finset.sum_singleton]
        exact max_le (by linarith [hw (partner t sgc0)]) (by positivity)
    · have := geo7 a N
      have h4 : 0 ≤ a / (6 * 7 ^ N) := by positivity
      linarith
  have h0 : 0 ≤ askD (DA (H := H)) N a t w := by
    unfold askD
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _
  unfold ASK
  rw [Finset.sum_eq_zero, hd, zero_add]
  · have hl : Real.log 7 ≤ 7 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have hl0 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
    nlinarith
  · intro p hp
    obtain ⟨-, hp2⟩ := Finset.mem_filter.1 hp
    exact absurd (by show InPhi (0 : E0 × H); simp [InPhi]) hp2.2.2.2.2
end Formalism.LFunctionChainParameters.LChain.ModelEv
