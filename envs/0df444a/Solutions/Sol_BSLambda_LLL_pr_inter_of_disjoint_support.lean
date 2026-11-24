-- Prove2me | solution 1 for BSLambda.LLL.pr_inter_of_disjoint_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:13:18.136885+00:00
-- url     : https://prove2.me/submissions/3963ba56-ed7d-4d56-a028-f30ef580e649

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
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_Determined_mem_glue_iff_left
public import Theorems.Thm_BSLambda_LLL_Determined_mem_glue_iff_right
public import Theorems.Thm_BSLambda_LLL_swapGlue_swapGlue
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
variable [∀ a, Nonempty (β a)]
namespace BSLambda.LLL
theorem _root_.solution {S T : Finset A} {E F : Finset (Cfg β)}
    (hE : Determined S E) (hF : Determined T F) (hST : Disjoint S T) :
    pr (E ∩ F) = pr E * pr F := by
  -- `swapGlue S` is a bijection between `(E ∩ F) ×ˢ univ` and `E ×ˢ F`
  have hcard : ((E ∩ F) ×ˢ (Finset.univ : Finset (Cfg β))).card = (E ×ˢ F).card := by
    refine Finset.card_nbij' (swapGlue S) (swapGlue S) ?_ ?_ (fun p _ ↦ swapGlue_swapGlue S p)
      (fun q _ ↦ swapGlue_swapGlue S q)
    all_goals
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_inter, Finset.mem_univ,
        and_true] at hp ⊢
      exact ⟨hE.mem_glue_iff_left.mpr hp.1, (hF.mem_glue_iff_right hST).mpr hp.2⟩
  rw [Finset.card_product, Finset.card_product, Finset.card_univ] at hcard
  have hcast : ((E ∩ F).card : ℝ) * (Fintype.card (Cfg β) : ℝ) = (E.card : ℝ) * (F.card : ℝ) :=
    mod_cast hcard
  rw [pr_eq_div, pr_eq_div, pr_eq_div, div_mul_div_comm, div_eq_div_iff card_cfg_pos_real.ne'
    (mul_ne_zero card_cfg_pos_real.ne' card_cfg_pos_real.ne'), ← hcast]
  ring
end BSLambda.LLL
