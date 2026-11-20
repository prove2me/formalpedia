-- Prove2me | solution 1 for DeletionCode.MaximalRuns.exists_maximal_run_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:19.787486+00:00
-- url     : https://prove2.me/submissions/ac1157c9-0deb-41b9-bb35-cfdaa562a758

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
import Theorems.Thm_DeletionCode_MaximalRuns_exists_maximal_run
import Theorems.Thm_DeletionCode_MaximalRuns_run_length_le_of_unique

set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (word : List Bool) (pos k : ℕ)
    (hpos : pos < word.length) (hx : KUnique (listLetters word) word.length k) :
    ∃ (pre suffix : List Bool) (rho : ℕ) (bit : Bool),
      0 < rho ∧ rho ≤ k ∧ word = pre ++ List.replicate rho bit ++ suffix ∧
      pre.length ≤ pos ∧ pos < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  obtain ⟨pre, suffix, rho, bit, hrho, heq, hstart, hstop, hleft, hright⟩ :=
    exists_maximal_run word pos hpos
  exact ⟨pre, suffix, rho, bit, hrho,
    run_length_le_of_unique word k hx pre suffix rho bit heq,
    heq, hstart, hstop, hleft, hright⟩
end DeletionCode.MaximalRuns
