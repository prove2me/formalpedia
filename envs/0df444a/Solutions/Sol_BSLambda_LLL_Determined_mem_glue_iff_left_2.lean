-- Prove2me | solution 2 for BSLambda.LLL.Determined.mem_glue_iff_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:12:44.727099+00:00
-- url     : https://prove2.me/submissions/f9dba08b-8faf-4a7b-af94-6d1713d30f35

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_mem

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
omit [Fintype A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)]
namespace BSLambda.LLL
namespace Determined
theorem _root_.solution {S : Finset A} {E : Finset (Cfg β)} (hE : Determined S E)
    {u v : Cfg β} : glue S u v ∈ E ↔ u ∈ E :=
  hE _ _ fun _ ha ↦ glue_apply_of_mem ha
end Determined
end BSLambda.LLL
