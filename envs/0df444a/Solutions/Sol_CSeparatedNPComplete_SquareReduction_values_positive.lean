-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.values_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:51.602167+00:00
-- url     : https://prove2.me/submissions/aa3cba38-5ea4-41df-b4b4-784226966395

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_lower_lt_upper

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) : ∀ i, 0 < values a i := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have h : 0 < upper a j := lt_of_le_of_lt (Nat.zero_le _) (lower_lt_upper a j)
    simp only [values, Fin.append_left]
    exact_mod_cast (show 0 < (upper a j + lower a j) ^ 2 by positivity)
  · intro j
    have h : 0 < upper a j - lower a j := Nat.sub_pos_of_lt (lower_lt_upper a j)
    simp only [values, Fin.append_right]
    exact_mod_cast (show 0 < (upper a j - lower a j) ^ 2 by positivity)
end CSeparatedNPComplete.SquareReduction
