-- Prove2me | solution 1 for BalanceSpecification.bsm_iff_entropy_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:18.259896+00:00
-- url     : https://prove2.me/submissions/59b3d53f-6df3-405b-9d73-21a0e44cac0c

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Theorems.Thm_BalanceSpecification_wordCount_one_le
public import Theorems.Thm_BalanceSpecification_wordCount_submultiplicative
public import Theorems.Thm_BalanceSpecification_Growth_bsm_iff_exp_ratio


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
        1 / c ≤ Real.exp ((n : ℝ) * entropy X hX) / wordCount (language X) n ∧
          Real.exp ((n : ℝ) * entropy X hX) / wordCount (language X) n ≤ 1 :=
  Growth.bsm_iff_exp_ratio (wordCount_one_le hX) (wordCount_submultiplicative X)
end BalanceSpecification
