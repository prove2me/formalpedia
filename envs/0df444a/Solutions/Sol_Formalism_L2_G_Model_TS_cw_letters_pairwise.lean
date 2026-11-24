-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cw_letters_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:58:13.249796+00:00
-- url     : https://prove2.me/submissions/5db32ee0-b451-4525-b46c-7e31babddaa1

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution :
    (cwLetters r n).Pairwise fun l l' => l'.1.val ≤ l.1.val ∧ l.2.2 ≠ l'.2.2 := by
  unfold cwLetters
  rw [List.pairwise_flatMap]
  constructor
  · intro s _
    rw [List.pairwise_filterMap]
    refine (List.pairwise_lt_finRange r).imp ?_
    intro a a' haa b hb b' hb'
    split_ifs at hb with h
    split_ifs at hb' with h'
    simp only [Option.some.injEq] at hb hb'
    subst hb hb'
    refine ⟨le_refl _, ?_⟩
    intro hc
    simp only [Prod.mk.injEq, and_true] at hc
    exact absurd hc (ne_of_lt haa)
  · rw [List.pairwise_reverse]
    refine (List.pairwise_lt_finRange n).imp ?_
    intro s s' hss x hx y hy
    simp only [List.mem_filterMap, List.mem_finRange, true_and] at hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    split_ifs at ha with h
    split_ifs at hb with h'
    simp only [Option.some.injEq] at ha hb
    subst ha hb
    refine ⟨le_of_lt hss, ?_⟩
    intro hc
    simp only [Prod.mk.injEq] at hc
    exact absurd hc.2 (ne_of_gt hss)
end Formalism.L2.G.Model.TS
