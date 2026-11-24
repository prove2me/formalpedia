-- Prove2me | solution 1 for BalanceSpecification.lexWords_shortlex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:14.354523+00:00
-- url     : https://prove2.me/submissions/bf5e0859-7e12-4403-90a7-7a3d3ad44146

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
namespace BalanceSpecification
theorem _root_.solution (n : ℕ) :
    (lexWords (A := A) n).Pairwise (List.Shortlex (· < ·)) := by
  apply ((Finset.sortedLT_sort (allWords (A := A) n)).pairwise).imp_of_mem
  intro u v hu hv huv
  exact List.Shortlex.of_lex ((mem_lexWords.mp hu).trans (mem_lexWords.mp hv).symm) huv
end BalanceSpecification
