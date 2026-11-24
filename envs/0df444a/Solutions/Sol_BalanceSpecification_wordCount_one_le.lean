-- Prove2me | solution 1 for BalanceSpecification.wordCount_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:02.881412+00:00
-- url     : https://prove2.me/submissions/bf16142b-3ac8-45bc-a6fc-cb2a7cbe7e71

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A} (hX : X.carrier.Nonempty) (n : ℕ) :
    (1 : ℝ) ≤ wordCount (language X) n := by
  exact_mod_cast wordCount_pos_of_nonempty hX n
end BalanceSpecification
