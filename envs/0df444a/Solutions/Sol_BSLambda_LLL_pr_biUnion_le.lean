-- Prove2me | solution 1 for BSLambda.LLL.pr_biUnion_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:53:17.434811+00:00
-- url     : https://prove2.me/submissions/1ece332b-165f-4d6a-803c-ab99cb8f4448

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_eq_div
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_card_cfg_pos_real
public import Theorems.Thm_BSLambda_LLL_pr_univ
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
variable [∀ a, Nonempty (β a)]
namespace BSLambda.LLL
theorem _root_.solution {κ : Type*} (T : Finset κ) (E : κ → Finset (Cfg β)) :
    pr (T.biUnion E) ≤ ∑ i ∈ T, pr (E i) := by
  simp only [pr_eq_div]
  rw [div_le_iff₀ card_cfg_pos_real, ← Finset.sum_div, div_mul_cancel₀ _ card_cfg_pos_real.ne']
  exact_mod_cast Finset.card_biUnion_le (s := T) (t := E)
end BSLambda.LLL
