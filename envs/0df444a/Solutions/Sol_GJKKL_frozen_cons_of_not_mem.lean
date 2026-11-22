-- Prove2me | solution 1 for GJKKL.frozen_cons_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:18.283993+00:00
-- url     : https://prove2.me/submissions/84bd5f51-0609-46a6-a997-3f266287a613

module
public import Definitions.Def_GJKKL_Greedy_Drift
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Theorems.Thm_GJKKL_covered_cons
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_dv_cons
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
attribute [local simp] GJKKL.Dv_nil
attribute [local simp] GJKKL.History.aliveBefore_cons
attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (F : ℕ → ℝ → ℝ) {v : V} {a : Finset V}
    {h : List (Finset V)} (hv : v ∉ covered h) (hva : v ∉ a) :
    frozen H F v (a :: h) =
      F (h.length + 1) ((dv H h v : ℝ) - ((Dv H h v).filter (fun f => ¬ Disjoint f a)).card) := by
  have hv' : v ∉ covered (a :: h) := by
    rw [covered_cons, mem_union]; tauto
  simp only [frozen, if_neg hv']
  congr 1
  have := dv_cons H a h v
  rw [eq_sub_iff_add_eq]
  exact_mod_cast this
end GJKKL
