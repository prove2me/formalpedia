-- Prove2me | solution 1 for BSLambda.LLL.Determined.mem_glue_iff_right
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:54:47.849089+00:00
-- url     : https://prove2.me/submissions/64ac9a95-82fb-46e5-8a7e-280460b28acf

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
omit [Fintype A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)]


theorem solution {S T : Finset A} {F : Finset (Cfg β)}
    (hF : Determined T F) (hST : Disjoint S T) {u v : Cfg β} : glue S u v ∈ F ↔ v ∈ F := by
  apply hF
  intro a ha
  have hn : a ∉ S := fun hs => Finset.disjoint_left.mp hST hs ha
  simp [glue,hn]
