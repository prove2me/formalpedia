-- Prove2me | solution 1 for BalanceSpecification.exp_mul_entropy_le_wordCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:47.756481+00:00
-- url     : https://prove2.me/submissions/2cde3a20-43e5-44f2-a22f-6d07ee693097

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Theorems.Thm_BalanceSpecification_wordCount_one_le
public import Theorems.Thm_BalanceSpecification_wordCount_submultiplicative
public import Theorems.Thm_BalanceSpecification_Growth_exp_mul_rate_le


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
    Real.exp ((n : ℝ) * entropy X hX) ≤ wordCount (language X) n :=
  Growth.exp_mul_rate_le (wordCount_one_le hX) (wordCount_submultiplicative X) n
end BalanceSpecification
