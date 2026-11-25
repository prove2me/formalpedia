-- Prove2me | solution 1 for Finset.exists_forall_not_of_lll
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:18.388261+00:00
-- url     : https://prove2.me/submissions/8e22ea91-c025-4f2c-a16e-4b659bed86d5

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
public import Theorems.Thm_Finset_exists_mem_forall_not_of_weight_lll
public import Theorems.Thm_Finset_bernoulliWeight_nonneg
public import Theorems.Thm_Finset_sum_bernoulliWeight


set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]
variable {E}
variable {E : ι → Finset α → Prop} [∀ i, DecidablePred (E i)]
namespace Finset
theorem _root_.solution (h0 : 0 ≤ p) (h1 : p ≤ 1) {I : Finset ι} {Γ : ι → Finset ι}
    (hL : Lopsided U p I E Γ) {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i ∈ I, U.bernoulliProb p (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∃ A ∈ U.powerset, ∀ i ∈ I, ¬E i A :=
  exists_mem_forall_not_of_weight_lll (Ω := U.powerset) (w := U.bernoulliWeight p)
    (fun A _ => bernoulliWeight_nonneg h0 h1 A) (sum_bernoulliWeight U p) hL hx0 hx1 hp
end Finset
