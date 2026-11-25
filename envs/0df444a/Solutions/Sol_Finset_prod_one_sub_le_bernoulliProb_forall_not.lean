-- Prove2me | solution 1 for Finset.prod_one_sub_le_bernoulliProb_forall_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:26.201874+00:00
-- url     : https://prove2.me/submissions/59ee54cd-3e26-442f-8504-d7d276173710

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
public import Theorems.Thm_Finset_prod_one_sub_le_weightProb_forall_not
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
theorem _root_.solution (h0 : 0 ≤ p) (h1 : p ≤ 1) {I : Finset ι}
    {Γ : ι → Finset ι} (hL : Lopsided U p I E Γ) {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1)
    (hp : ∀ i ∈ I, U.bernoulliProb p (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∏ i ∈ I, (1 - x i) ≤ U.bernoulliProb p (Avoids E I) :=
  prod_one_sub_le_weightProb_forall_not (Ω := U.powerset) (w := U.bernoulliWeight p)
    (fun A _ => bernoulliWeight_nonneg h0 h1 A) (sum_bernoulliWeight U p) hL hx0 hx1 hp
end Finset
