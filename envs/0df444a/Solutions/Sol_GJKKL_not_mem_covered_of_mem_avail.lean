-- Prove2me | solution 1 for GJKKL.not_mem_covered_of_mem_avail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:52.14612+00:00
-- url     : https://prove2.me/submissions/92e5810c-ba2d-49d6-b1a8-24f95cd030dd

module
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Definitions.Def_GJKKL_Trajectory_Trend
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Theorems.Thm_GJKKL_mem_avail_iff_uncovered


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} {h : List (Finset V)}
    {f : Finset V} (hf : f ∈ avail H h) {u : V} (hu : u ∈ f) : u ∉ covered h :=
  Finset.disjoint_left.mp (mem_avail_iff_uncovered.mp hf).2 hu
end GJKKL
