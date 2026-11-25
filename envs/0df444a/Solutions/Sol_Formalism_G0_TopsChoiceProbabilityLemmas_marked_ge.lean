-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.marked_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:12.633175+00:00
-- url     : https://prove2.me/submissions/487d9bf8-827b-4f51-988e-09296b087137

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_forall_eq_prod
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_cell_sub_tile
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_cell_disjoint
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_marked_iff
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_dep_EC
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prod_g
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_EC_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution {U : Finset ℕ} {δ : ℝ} {r u s : ℕ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (hT : tile r u s ⊆ U) :
    markedBound δ r u ≤ P U δ (fun t => Marked t r u s) := by
  classical
  have hcU : ∀ c ∈ Icc 1 (6 * r + 1), cell r u s c ⊆ U :=
    fun c hc => (cell_sub_tile (mem_Icc.1 hc).1 (mem_Icc.1 hc).2).trans hT
  have e : P U δ (fun t => Marked t r u s) =
      ∏ c ∈ Icc 1 (6 * r + 1), P U δ (EC r u s c) := by
    rw [← prob_forall_eq_prod δ (Icc 1 (6 * r + 1)) (cell r u s) hcU
      (fun c hc c' hc' hne => cell_disjoint (mem_Icc.1 hc).1 (mem_Icc.1 hc').1 hne)
      (EC r u s) (fun c _ => dep_EC r u s c)]
    congr 1
    funext t
    exact propext (marked_iff t r u s)
  rw [e]
  have hg := prod_g ((1 - δ) ^ u) (((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)) (3 * r)
  rw [show 2 * (3 * r) + 1 = 6 * r + 1 by ring] at hg
  unfold markedBound
  rw [← hg]
  apply prod_le_prod
  · intro c _
    have : 0 ≤ 1 - δ := by linarith
    split_ifs
    · positivity
    · positivity
  · intro c hc
    exact EC_ge h0 h1 (mem_Icc.1 hc).1 (hcU c hc)
end Formalism.G0.TopsChoiceProbabilityLemmas
