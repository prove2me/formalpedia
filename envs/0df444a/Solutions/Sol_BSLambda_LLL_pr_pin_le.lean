-- Prove2me | solution 1 for BSLambda.LLL.pr_pin_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:54.273235+00:00
-- url     : https://prove2.me/submissions/f685ab2d-7fad-4a29-8197-259abb00aa23

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_pin_eq

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
variable [∀ a, Nonempty (β a)]
namespace BSLambda.LLL
theorem _root_.solution (T : Finset A) (s : (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ a ∈ T, (s a).card ≤ m) :
    pr (Finset.univ.filter fun ω : Cfg β => ∀ a ∈ T, ω a ∈ s a)
      ≤ ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) := by
  rw [pr_pin_eq]
  gcongr with a ha
  exact_mod_cast hm a ha
end BSLambda.LLL
