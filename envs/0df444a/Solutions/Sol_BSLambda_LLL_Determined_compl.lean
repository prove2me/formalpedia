-- Prove2me | solution 1 for BSLambda.LLL.Determined.compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:40.080809+00:00
-- url     : https://prove2.me/submissions/e318e56e-cb0d-40ef-b1bd-a3cba27b8847

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
namespace BSLambda.LLL
namespace Determined
theorem _root_.solution {S : Finset A} {E : Finset (Cfg β)} (hE : Determined S E) :
    Determined S Eᶜ := by
  intro ω ω' h
  simp only [Finset.mem_compl]
  exact not_congr (hE ω ω' h)
end Determined
end BSLambda.LLL
