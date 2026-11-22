-- Prove2me | solution 1 for GJKKL.dv_eq_zero_of_covered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:27.816557+00:00
-- url     : https://prove2.me/submissions/de66e3db-e95c-47f1-8dd6-7d6f2c7caac5

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Theorems.Thm_GJKKL_mem_Dv
public import Theorems.Thm_GJKKL_mem_avail_iff_uncovered


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} {h : List (Finset V)} {v : V}
    (hv : v ∈ covered h) : dv H h v = 0 := by
  rw [dv, card_eq_zero, eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_Dv, mem_avail_iff_uncovered] at he
  exact Finset.disjoint_left.mp he.1.2 he.2 hv
end GJKKL
