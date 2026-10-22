-- Prove2me | solution 1 for DirS.dir_sid_needs_edge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:43:17.426405+00:00
-- url     : https://prove2.me/submissions/50112211-8971-4caf-8026-3ff93bf73b71

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw
open DirS

/-- The single directed edge 0 -> 1. -/
def g73t_K2 : OriGraph 2 where
  edge x y := decide (x.val = 0 ∧ y.val = 1)
  no_loop := by decide
  no_two_cycle := by decide

theorem g73t_K2_edgeCount : g73t_K2.edgeCount = 1 := by decide

theorem solution {m : ℕ} (B : OriGraph m) (h : DirSidorenko B) :
    homToEdge B := by
  have h1 := h 2 g73t_K2
  have hd : g73t_K2.dirDens = 1 / 4 := by
    unfold OriGraph.dirDens
    rw [g73t_K2_edgeCount]
    norm_num
  rw [hd] at h1
  have hpos : (0 : ℝ) < (1 / 4 : ℝ) ^ (B.edgeCount : ℝ) := by positivity
  have hc : B.homCount g73t_K2 ≠ 0 := by
    intro h0
    unfold OriGraph.homDens at h1
    rw [h0] at h1
    simp at h1
    exact absurd h1 (not_le.mpr (by positivity))
  unfold OriGraph.homCount at hc
  obtain ⟨f, hf⟩ := Finset.card_ne_zero.mp hc
  rw [Finset.mem_filter] at hf
  have hf2 := hf.2
  refine ⟨fun x => decide ((f x).val = 1), ?_⟩
  intro x y hxy
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at hf2
  have := hf2 x y
  rw [hxy] at this
  simp [g73t_K2] at this
  obtain ⟨h0, h1⟩ := this
  simp [h0, h1]
