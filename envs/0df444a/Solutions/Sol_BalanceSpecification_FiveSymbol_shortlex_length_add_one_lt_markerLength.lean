-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.shortlex_length_add_one_lt_markerLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:18.279178+00:00
-- url     : https://prove2.me/submissions/f5d1949c-ce92-4d49-9dd8-4cd6468d8efd

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_index_add_one_lt_markerLength
public import Theorems.Thm_BalanceSpecification_length_shortlexWord_le


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution {j : ℕ} (hj : 1 ≤ j) :
    (shortlexWord (A := Alphabet) j).length + 1 < markerLength j := by
  have := length_shortlexWord_le (A := Alphabet) j
  have := index_add_one_lt_markerLength hj
  omega
end BalanceSpecification.FiveSymbol
