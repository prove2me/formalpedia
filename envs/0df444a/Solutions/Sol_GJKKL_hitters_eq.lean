-- Prove2me | solution 1 for GJKKL.hitters_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:48.302077+00:00
-- url     : https://prove2.me/submissions/998d4294-fbc5-4411-b832-009be9350007

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
public import Theorems.Thm_GJKKL_mem_sdiff_Dv
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
attribute [local simp] GJKKL.Dv_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} {h : List (Finset V)} {v : V} {f : Finset V} :
    hitters H h v f =
      (f.erase v).biUnion (fun u => (avail H h \ Dv H h v).filter (fun a => u ∈ a)) := by
  ext a
  simp only [hitters, mem_filter, mem_biUnion, mem_erase, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨ha, u, huf, hua⟩
    refine ⟨u, ⟨fun huv => ?_, huf⟩, ha, hua⟩
    subst huv
    exact (mem_sdiff_Dv.mp ha).2 hua
  · rintro ⟨u, ⟨_, huf⟩, ha, hua⟩
    exact ⟨ha, u, huf, hua⟩
end GJKKL
