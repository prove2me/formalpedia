-- Prove2me | solution 1 for BSLambda.LLL.Determined.inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:37.615868+00:00
-- url     : https://prove2.me/submissions/36c27016-1678-4dc6-8471-b866d5e1a691

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
omit [(a : A) → Fintype (β a)]
namespace BSLambda.LLL
namespace Determined
theorem _root_.solution {S T : Finset A} {E F : Finset (Cfg β)} (hE : Determined S E)
    (hF : Determined T F) : Determined (S ∪ T) (E ∩ F) := by
  intro ω ω' h
  simp only [Finset.mem_inter]
  exact and_congr (hE ω ω' fun a ha ↦ h a (Finset.mem_union_left _ ha))
    (hF ω ω' fun a ha ↦ h a (Finset.mem_union_right _ ha))
end Determined
end BSLambda.LLL
