-- Prove2me | solution 1 for BalanceSpecification.bsm_iff_bounded_wordCount_of_entropy_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:38.113362+00:00
-- url     : https://prove2.me/submissions/468348f2-744a-4bfe-88cb-5b5a488c7d8e

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Theorems.Thm_BalanceSpecification_wordCount_one_le
public import Theorems.Thm_BalanceSpecification_wordCount_submultiplicative
public import Theorems.Thm_BalanceSpecification_Growth_bsm_iff_bddAbove_of_rate_zero


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) (hh : entropy X hX = 0) :
    BoundedlySupermultiplicative (language X) ↔
      BddAbove (Set.range fun n => (wordCount (language X) n : ℝ)) :=
  Growth.bsm_iff_bddAbove_of_rate_zero (wordCount_one_le hX)
    (wordCount_submultiplicative X) hh
end BalanceSpecification
