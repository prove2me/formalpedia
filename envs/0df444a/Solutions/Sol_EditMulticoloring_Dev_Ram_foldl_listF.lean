-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.foldl_listF
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:08.777181+00:00
-- url     : https://prove2.me/submissions/2083789c-841c-4041-994a-6d6c5a6ba900

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section
-- module Solutions.EditMulticoloring.RamEnum3
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator: main theorem, size bound, toy clients (q379, Part L)

* `enumScripts_spec` — the fold specification of `enumScripts q s cfg body`;
* `visits_length_le` — `(visits s x).length ≤ ∑ i ∈ range (s+1), (2q(|x|+s+1))^i`;
* toy clients `countProg` (count the visited words of length `|x|` other than `x`) and
  `listProg` (store them as a 2-D array, word `j` at offsets `j * S`), both proved.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Size of the visit list -/

/-! ## Toy client (a): counting -/

section Toys
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## Toy client (b): the list of visited words of length `|x|` other than `x` -/

theorem foldl_listF_oai {q : ℕ} (x : Word q) (l acc : List (Word q)) :
    l.foldl (listF x) acc = acc ++ l.filter (fun w => decide (w.length = x.length ∧ w ≠ x)) := by
  induction l generalizing acc with
  | nil => simp
  | cons w l ih =>
    rw [List.foldl_cons, ih, List.filter_cons]
    unfold listF
    by_cases h : w.length = x.length ∧ w ≠ x
    · rw [if_pos h, if_pos (by simpa using h)]; simp
    · rw [if_neg h, if_neg (by simpa using h)]

end Toys

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.foldl_listF_oai := @EditMulticoloring.Dev.Ram.foldl_listF_oai
