-- Prove2me | solution 1 for GJKKL.TrackHyp.bad_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:49.738523+00:00
-- url     : https://prove2.me/submissions/2090d92a-0b34-49bd-9076-8a72eec66abe

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_avail_nonempty
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_dv_nil
public import Theorems.Thm_GJKKL_frozen_of_uncovered
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
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
open GJKKL.TrackHyp
variable {H : Finset (Finset V)} {k c : ℕ} {dh δ : ℕ → ℝ} {T : ℕ} {B lam C s : ℝ}
  (hyp : TrackHyp H k c dh δ T B lam C s)
include hyp
namespace GJKKL.TrackHyp
theorem _root_.solution {h : List (Finset V)} (hT : h.length < T)
    (hal : AliveBefore (GoodState H dh δ) h) (hbad : ¬ GoodState H dh δ h) :
    ¬ IsGreedySeq H h ∨ ∃ v ∈ (univ : Finset V),
      (lam ≤ upperProc H dh δ v h - upperProc H dh δ v [] ∧ AliveBefore (GoodState H dh δ) h) ∨
      (lam ≤ lowerProc H dh δ v h - lowerProc H dh δ v [] ∧ AliveBefore (GoodState H dh δ) h) := by
  by_cases hgr : IsGreedySeq H h
  · right
    have hnt : ¬ Tracked H dh δ h := fun ht => hbad ⟨hgr, ht, hyp.avail_nonempty hT hgr ht⟩
    unfold Tracked at hnt
    push_neg at hnt
    obtain ⟨u, hu, hdev⟩ := hnt
    refine ⟨u, mem_univ u, ?_⟩
    have hinit := hyp.init u
    rw [abs_le] at hinit
    have h0u : upperProc H dh δ u [] = 1 * (degree H u : ℝ) + (-dh 0 - δ 0) := by
      simp [upperProc, frozen, dv_nil]
    have h0l : lowerProc H dh δ u [] = (-1) * (degree H u : ℝ) + (dh 0 - δ 0) := by
      simp [lowerProc, frozen, dv_nil]
    have hhu : upperProc H dh δ u h = 1 * (dv H h u : ℝ) + (-dh h.length - δ h.length) :=
      frozen_of_uncovered H _ u hu
    have hhl : lowerProc H dh δ u h = (-1) * (dv H h u : ℝ) + (dh h.length - δ h.length) :=
      frozen_of_uncovered H _ u hu
    rcases lt_abs.mp hdev with hpos | hneg
    · left; refine ⟨?_, hal⟩; rw [hhu, h0u]; linarith
    · right; refine ⟨?_, hal⟩; rw [hhl, h0l]; linarith
  · left; exact hgr
end GJKKL.TrackHyp
