-- Prove2me | solution 1 for BalanceSpecification.exists_wordCount_exp_bound_of_entropy_lt_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:38.460568+00:00
-- url     : https://prove2.me/submissions/b0a1d7b0-0ead-4b49-b2e9-9b2f50ee2047

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Theorems.Thm_BalanceSpecification_Growth_exists_exp_bound_of_rate_lt_log
public import Theorems.Thm_BalanceSpecification_wordCount_one_le
public import Theorems.Thm_BalanceSpecification_wordCount_submultiplicative


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution
    {A : Type*} [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) {γ : ℝ} (hγ : 0 < γ)
    (hgap : entropy X hX < Real.log γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤ C * γ ^ n :=
  Growth.exists_exp_bound_of_rate_lt_log (wordCount_one_le hX)
    (wordCount_submultiplicative X) hγ hgap
end BalanceSpecification
