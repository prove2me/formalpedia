-- Prove2me | solution 1 for GJKKL.weight_cons_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:19.962232+00:00
-- url     : https://prove2.me/submissions/cf2a11c2-55ab-48a0-b5d3-1b55c7638365

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_greedyKernel_K
public import Theorems.Thm_GJKKL_History_weight_cons
attribute [local simp] GJKKL.History.weight_cons



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} {a : Finset V} {h : List (Finset V)}
    (ha : a ∈ avail H h) :
    weight (greedyKernel H) (a :: h) = weight (greedyKernel H) h / (avail H h).card := by
  rw [weight_cons, greedyKernel_K, if_pos ha, div_eq_mul_inv]
end GJKKL
