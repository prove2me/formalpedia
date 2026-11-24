-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.entropy_eq_source_of_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:33.334525+00:00
-- url     : https://prove2.me/submissions/242d0f69-ff6e-4877-90b9-115596c388bc

module
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
public import Theorems.Thm_BalanceSpecification_MarkerExtension_entropy_le_of_uniform_exp_bound
public import Theorems.Thm_BalanceSpecification_MarkerExtension_source_entropy_le


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {hY : Y.carrier.Nonempty} {K : ℝ}
    (hbound : ∀ n : ℕ, (wordCount (language (shift M hM x s)) n : ℝ) ≤
      K * Real.exp ((n : ℝ) * entropy Y hY)) :
    entropy (shift M hM x s) (shift_nonempty M hM x s) = entropy Y hY :=
  le_antisymm (entropy_le_of_uniform_exp_bound (shift_nonempty M hM x s) hbound)
    (source_entropy_le M hM x s hY)
end BalanceSpecification.MarkerExtension
