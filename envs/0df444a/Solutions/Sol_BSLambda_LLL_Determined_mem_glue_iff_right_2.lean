-- Prove2me | solution 2 for BSLambda.LLL.Determined.mem_glue_iff_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:12:45.2138+00:00
-- url     : https://prove2.me/submissions/d1d5c38e-8a9e-455c-a23f-247031395c7b

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
omit [Fintype A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)]
namespace BSLambda.LLL
namespace Determined
theorem _root_.solution {S T : Finset A} {F : Finset (Cfg β)}
    (hF : Determined T F) (hST : Disjoint S T) {u v : Cfg β} : glue S u v ∈ F ↔ v ∈ F :=
  hF _ _ fun _ ha ↦ glue_apply_of_notMem (Finset.disjoint_right.mp hST ha)
end Determined
end BSLambda.LLL
