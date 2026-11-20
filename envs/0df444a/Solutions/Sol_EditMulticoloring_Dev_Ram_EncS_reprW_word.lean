-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EncS.reprW_word
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:05.987304+00:00
-- url     : https://prove2.me/submissions/701e56b0-4856-449a-938c-c9718de8204c

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_reprW_spec

section
-- module Solutions.EditMulticoloring.RamEncodeS1
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-! Verbatim copy of `RamShort.lean` (q379, Part S) in namespace `EditMulticoloring.Dev.Ram.EncS`:
the original clashes with `RamColor` on the names `value_lt` and `visBound`, so the two chains
cannot be imported together; the encoder uses this copy. -/

/-!
# Short table, part 1: words, values, representations, greedy (q379, Part S)

* `value_cons`, `value_lt`, `value_inj` — `value` is a bijection from words of length `l`
  onto `[0, q^l)`;
* `repr_length`, `repr_getElem`, `value_repr`, `repr_value` — `Code.repr q l` is its inverse;
* `words_eq` — `words q l = (List.range (q^l)).map (Code.repr q l)`;
* `greedy` facts: sublist of the input, no duplicates, lengths;
* the RAM routine `reprW` writing the digits of a number (`repr`) into an array.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

/-! ## `value` -/

/-! ## `repr` -/

theorem repr_eq_map {q : ℕ} (hq : 0 < q) (l N : ℕ) :
    Code.repr q l N = (List.range l).map (fun i => (⟨(N / q ^ (l - 1 - i)) % q, Nat.mod_lt _ hq⟩ : Fin q)) := by
  unfold Code.repr
  rw [← List.filterMap_eq_map]
  apply List.filterMap_congr
  intro i _
  simp [Nat.mod_lt _ hq]

theorem repr_length {q : ℕ} (hq : 0 < q) (l N : ℕ) : (Code.repr q l N).length = l := by
  rw [repr_eq_map hq]; simp

theorem repr_getElem {q : ℕ} (hq : 0 < q) (l N i : ℕ) (hi : i < (Code.repr q l N).length) :
    ((Code.repr q l N)[i]).val = (N / q ^ (l - 1 - i)) % q := by
  simp only [repr_eq_map hq, List.getElem_map, List.getElem_range]

/-! ## `words` -/

/-! ## `greedy` -/

/-! ## Writing the digits of a number -/

section Repr
variable (inp : ℕ → ℕ) (B : ℕ)

/-- `reprW` stores the word `repr q n V`. -/
theorem reprW_word_oai {q : ℕ} (hq : 0 < q) (r : ℕ) (s : HS) (hQ : s.regs (r + 4) = q)
    (hP : s.regs (r + 2) = q ^ s.regs (r + 3)) :
    WordAt ((reprW r).exec inp s) (s.regs r) 0 (Code.repr q (s.regs (r + 3)) (s.regs (r + 1))) := by
  have := (reprW_spec inp 0 r s _ (by omega) (by rw [hQ]; exact hP) le_rfl).1
  intro i hi
  rw [repr_length hq] at hi
  rw [zero_add, this i hi, repr_getElem hq, hQ]

end Repr

end EditMulticoloring.Dev.Ram.EncS
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.EncS.reprW_word_oai := @EditMulticoloring.Dev.Ram.EncS.reprW_word_oai
