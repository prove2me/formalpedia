-- Prove2me | solution 1 for DeletionCode.MaximalRuns.exists_insertion_run_at_gap_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:57.817168+00:00
-- url     : https://prove2.me/submissions/de824842-3f4c-4831-856c-c18e0df4f690

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
import Theorems.Thm_DeletionCode_MaximalRuns_exists_insertion_run_unique

set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (word : List Bool) (pos : ℕ) (bit : Bool)
    (k : ℕ) (hpos : pos ≤ word.length)
    (hx : KUnique (listLetters word) word.length k) :
    ∃ (pre suffix : List Bool) (rho : ℕ),
      0 < rho ∧ rho ≤ k + 1 ∧
      word.take pos ++ bit :: word.drop pos = pre ++ List.replicate rho bit ++ suffix ∧
      word = pre ++ List.replicate (rho - 1) bit ++ suffix ∧
      pre.length ≤ pos ∧ pos < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  have htake : (word.take pos).length = pos := by
    simp only [List.length_take, Nat.min_eq_left hpos]
  have hx' : KUnique (listLetters (word.take pos ++ word.drop pos))
      (word.take pos ++ word.drop pos).length k := by
    simpa only [List.take_append_drop] using hx
  simpa only [List.take_append_drop, htake] using
    exists_insertion_run_unique (word.take pos) (word.drop pos) bit k hx'
end DeletionCode.MaximalRuns
