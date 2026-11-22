-- Prove2me | solution 1 for GJKKL.mem_avail_iff_uncovered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:15.960806+00:00
-- url     : https://prove2.me/submissions/05ac5694-5000-43f6-8dc6-8121969568c0

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_mem_covered

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} {h : List (Finset V)} {e : Finset V} :
    e ∈ avail H h ↔ e ∈ H ∧ Disjoint e (covered h) := by
  rw [mem_avail, Finset.disjoint_right]
  constructor
  · rintro ⟨he, hd⟩
    refine ⟨he, fun v hv hve => ?_⟩
    obtain ⟨f, hf, hvf⟩ := mem_covered.mp hv
    exact Finset.disjoint_left.mp (hd f hf) hve hvf
  · rintro ⟨he, hd⟩
    refine ⟨he, fun f hf => Finset.disjoint_left.mpr fun v hve hvf => ?_⟩
    exact hd (mem_covered.mpr ⟨f, hf, hvf⟩) hve
end GJKKL
