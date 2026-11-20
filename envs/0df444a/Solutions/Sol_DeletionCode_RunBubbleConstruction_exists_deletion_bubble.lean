-- Prove2me | solution 1 for DeletionCode.RunBubbleConstruction.exists_deletion_bubble
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:14.956859+00:00
-- url     : https://prove2.me/submissions/58f84847-09b2-4c49-87ac-6317c43f28ef

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
import Theorems.Thm_DeletionCode_RunBubbleConstruction_TrimmedRun_long_eq
import Theorems.Thm_DeletionCode_RunBubbleConstruction_TrimmedRun_short_eq
import Theorems.Thm_DeletionCode_RunBubbleConstruction_TrimmedRun_before_length
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
import Theorems.Thm_DeletionCode_MaximalRuns_eraseIdx_in_run
import Theorems.Thm_DeletionCode_MaximalRuns_exists_maximal_run_unique

section
namespace DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
namespace TrimmedRun
variable {k rho : ℕ} {pre suffix : List Bool} {bit : Bool} {orientation : Orientation}
end TrimmedRun
namespace LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
end LocalBubble
private theorem interior_flanks (k rho pos : ℕ) (pre suffix : List Bool)
    (hrho : rho ≤ k + 1) (hstart : pre.length ≤ pos)
    (hstop : pos < pre.length + rho)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ pre.length + rho + suffix.length) :
    windowLength k - rho ≤ pre.length ∧
      windowLength k - rho ≤ suffix.length ∧ 0 < pre.length ∧ 0 < suffix.length := by
  unfold windowLength at *
  omega
end DeletionCode.RunBubbleConstruction
end

set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
namespace DeletionCode.RunBubbleConstruction
theorem _root_.solution (word : List Bool) (pos k : ℕ)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    Nonempty (LocalBubble k word (word.eraseIdx pos) pos .deletion) := by
  have hpos : pos < word.length := by
    unfold windowLength at hright
    omega
  obtain ⟨pre, suffix, rho, bit, hrho, hrho', hword, hstart, hstop, hpre, hsuffix⟩ :=
    exists_maximal_run_unique word pos k hpos hx
  have hlength := congrArg List.length hword
  simp only [List.length_append, List.length_replicate] at hlength
  have hmargins := interior_flanks k rho pos pre suffix (by omega) hstart hstop
    hleft (by omega)
  have hpreBit : pre.getLast? = some (!bit) := by
    rcases hpre with hempty | hbit
    · subst pre
      simp at hmargins
    · exact hbit
  have hsuffixBit : suffix.head? = some (!bit) := by
    rcases hsuffix with hempty | hbit
    · subst suffix
      simp at hmargins
    · exact hbit
  let r := trimRun k pre suffix rho bit .deletion (by omega) (by omega)
    hmargins.1 hmargins.2.1 hpreBit hsuffixBit
  have hshort : word.eraseIdx pos = pre ++ List.replicate (rho - 1) bit ++ suffix := by
    rw [hword]
    exact eraseIdx_in_run pre suffix rho bit pos hstart hstop
  have hbefore := r.before_length
  have hrhoL : rho ≤ windowLength k := by unfold windowLength; omega
  refine ⟨{
    bubble := r.bubble
    before := r.before
    after := r.after
    orientation_eq := r.orientation_eq
    source_eq := ?_
    target_eq := ?_
    left_boundary := r.left_boundary
    right_boundary := r.right_boundary
    edit_start := ?_
    edit_stop := ?_
  }⟩
  · simpa only [BubbleWord.negativeWord, r.orientation_eq] using hword.trans r.long_eq
  · simpa only [BubbleWord.positiveWord, r.orientation_eq] using hshort.trans r.short_eq
  · rw [r.bubble.left_length, r.rho_eq]
    omega
  · omega
end DeletionCode.RunBubbleConstruction
