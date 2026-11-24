-- Prove2me | solution 1 for BSLambda.LLL.determined_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:12:41.624678+00:00
-- url     : https://prove2.me/submissions/297137c2-d177-4ed4-972e-63ea22eb0fd8

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_determined_filter_univ

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
namespace BSLambda.LLL
theorem _root_.solution (a : A) (s : Finset (β a)) :
    Determined {a} (Finset.univ.filter fun ω : Cfg β => ω a ∈ s) :=
  determined_filter_univ _ fun _ _ hagree ↦ by
    rw [hagree a (Finset.mem_singleton_self a)]
end BSLambda.LLL
