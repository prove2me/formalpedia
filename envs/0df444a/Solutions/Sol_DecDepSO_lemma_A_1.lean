-- Prove2me | solution 1 for DecDepSO.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:49:57.601691+00:00
-- url     : https://prove2.me/submissions/eb7cafde-81c0-457b-a391-d3a0b9e2d964

import Mathlib

theorem solution (δ : ℕ → ℝ) (hδ : ∀ t, 0 < δ t ∧ δ t < 1) (t : ℕ) :
    (∑ i ∈ Finset.Icc 1 t, δ i / ∏ j ∈ Finset.Icc 1 i, (1 - δ j)) + 1 =
      1 / ∏ i ∈ Finset.Icc 1 t, (1 - δ i) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hP : 0 < ∏ i ∈ Finset.Icc 1 t, (1 - δ i) :=
      Finset.prod_pos fun i _ => by linarith [(hδ i).2]
    have h1 : 0 < 1 - δ (t + 1) := by linarith [(hδ (t + 1)).2]
    rw [Finset.sum_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega),
      add_right_comm, ih]
    field_simp
    ring_nf
