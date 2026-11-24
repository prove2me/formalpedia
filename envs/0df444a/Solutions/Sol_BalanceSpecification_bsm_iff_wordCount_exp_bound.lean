-- Prove2me | solution 1 for BalanceSpecification.bsm_iff_wordCount_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:40.989119+00:00
-- url     : https://prove2.me/submissions/04c6bd68-4c72-4cc9-8949-98d4fdf26731

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Theorems.Thm_BalanceSpecification_wordCount_one_le
public import Theorems.Thm_BalanceSpecification_wordCount_submultiplicative
public import Theorems.Thm_BalanceSpecification_Growth_bsm_iff_uniform_exp_bound


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A} (hX : X.carrier.Nonempty) :
    BoundedlySupermultiplicative (language X) ↔
      ∃ c : ℝ, 1 ≤ c ∧ ∀ n : ℕ,
        (wordCount (language X) n : ℝ) ≤ c * Real.exp ((n : ℝ) * entropy X hX) :=
  Growth.bsm_iff_uniform_exp_bound (wordCount_one_le hX) (wordCount_submultiplicative X)
end BalanceSpecification
