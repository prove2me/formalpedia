-- Prove2me | solution 1 for BSLambda.LLL.pr_avoid_pos_two_type
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:57.849632+00:00
-- url     : https://prove2.me/submissions/5b6ac074-95fa-4d0f-b37b-bc68a1a50487

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Theorems.Thm_BSLambda_LLL_mem_nbr
public import Theorems.Thm_BSLambda_LLL_mem_avoid
public import Theorems.Thm_BSLambda_LLL_avoid_empty
public import Theorems.Thm_BSLambda_LLL_pr_avoid_pos
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ


attribute [local simp] BSLambda.LLL.mem_nbr
attribute [local simp] BSLambda.LLL.mem_avoid
attribute [local simp] BSLambda.LLL.avoid_empty

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace BSLambda.LLL
theorem _root_.solution (Ev : I → Finset (Cfg β)) (supp : I → Finset A)
    (hdet : ∀ i, Determined (supp i) (Ev i)) (ty : I → Bool)
    (p x : Bool → ℝ) (D : Bool → Bool → ℕ)
    (hp : ∀ i, pr (Ev i) ≤ p (ty i))
    (hD : ∀ i t, ((nbr supp i).filter fun j ↦ ty j = t).card ≤ D (ty i) t)
    (hx0 : ∀ t, 0 < x t) (hx1 : ∀ t, x t < 1)
    (hcond : ∀ t, p t ≤ x t * (1 - x false) ^ D t false * (1 - x true) ^ D t true) :
    0 < pr (Finset.univ.filter fun ω ↦ ∀ i, ω ∉ Ev i) := by
  refine pr_avoid_pos Ev supp (fun i ↦ x (ty i)) hdet (fun i ↦ hx0 _) (fun i ↦ hx1 _) fun i ↦ ?_
  set T : Finset I := nbr supp i
  have hnn (t : Bool) : (0 : ℝ) ≤ 1 - x t := sub_nonneg.mpr (hx1 t).le
  -- each type class contributes the constant factor `1 - x t`, raised to the size of that class
  have hc (t : Bool) : (∏ j ∈ T.filter fun j ↦ ty j = t, (1 - x (ty j)))
      = (1 - x t) ^ (T.filter fun j ↦ ty j = t).card :=
    (Finset.prod_congr rfl fun j hj ↦ by rw [(Finset.mem_filter.mp hj).2]).trans
      (Finset.prod_const _)
  have hb (t : Bool) : (1 - x t) ^ D (ty i) t
      ≤ (1 - x t) ^ (T.filter fun j ↦ ty j = t).card :=
    pow_le_pow_of_le_one (hnn t) (sub_le_self _ (hx0 t).le) (hD i t)
  -- splitting the neighbourhood product into its two type classes
  have hprod : (1 - x false) ^ D (ty i) false * (1 - x true) ^ D (ty i) true
      ≤ ∏ j ∈ T, (1 - x (ty j)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not T (fun j ↦ ty j = false)]
    simp only [Bool.not_eq_false, hc false, hc true]
    exact mul_le_mul (hb false) (hb true) (pow_nonneg (hnn true) _) (pow_nonneg (hnn false) _)
  calc pr (Ev i) ≤ p (ty i) := hp i
    _ ≤ x (ty i) * (1 - x false) ^ D (ty i) false * (1 - x true) ^ D (ty i) true := hcond (ty i)
    _ = x (ty i) * ((1 - x false) ^ D (ty i) false * (1 - x true) ^ D (ty i) true) :=
        mul_assoc _ _ _
    _ ≤ x (ty i) * ∏ j ∈ T, (1 - x (ty j)) := mul_le_mul_of_nonneg_left hprod (hx0 (ty i)).le
end BSLambda.LLL
