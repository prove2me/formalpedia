-- Prove2me | solution 1 for Finset.exists_mem_forall_not_of_weight_lll
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:25.203915+00:00
-- url     : https://prove2.me/submissions/e46dc7ba-e0be-413f-983f-d40df7031ab4

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
public import Theorems.Thm_Finset_prod_one_sub_le_weightProb_forall_not

set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]
variable {E}
variable {Ω : Finset β} {w : β → ℝ}
namespace Finset
theorem _root_.solution (hw0 : ∀ a ∈ Ω, 0 ≤ w a)
    (hw1 : ∑ a ∈ Ω, w a = 1) {I : Finset ι} {Γ : ι → Finset ι} (hL : LopsidedWeights Ω w I E Γ)
    {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i ∈ I, Ω.weightProb w (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∃ a ∈ Ω, ∀ i ∈ I, ¬E i a := by
  have hpos : 0 < Ω.weightProb w (Avoids E I) :=
    (prod_pos fun i _ => by linarith [hx1 i]).trans_le
      (prod_one_sub_le_weightProb_forall_not hw0 hw1 hL hx0 (fun i => (hx1 i).le) hp)
  obtain ⟨a, ha, -⟩ := exists_ne_zero_of_sum_ne_zero hpos.ne'
  exact ⟨a, (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩
end Finset
