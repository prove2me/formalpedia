-- Prove2me | solution 1 for DRBaseline.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:52:27.897673+00:00
-- url     : https://prove2.me/submissions/43b6cd02-4d8a-4f7c-88e9-d372ee548caa

import Mathlib
import Definitions.Def_DRBaseline_IsCustomerOptimal

open DRBaseline in
theorem solution (Ω cs b r ω x : ℝ) (hΩ : 0 < Ω) (hcs : 0 < cs) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hω0 : 0 ≤ ω) (hω2 : ω ≤ 2 * Ω) (hx : DRBaseline.IsCustomerOptimal cs b r ω x) :
    (ω < b → x < DRBaseline.estReduction b ω x) ∧ (b ≤ ω → DRBaseline.estReduction b ω x ≤ x) := by
  obtain ⟨hxω, hopt⟩ := hx
  have h0 := hopt 0 hω0
  unfold DRBaseline.customerObj DRBaseline.estReduction at h0
  have hx0 : 0 ≤ x := by
    by_contra hneg
    push_neg at hneg
    have hm : max (b - (ω - x)) 0 ≤ max (b - (ω - 0)) 0 := max_le_max (by linarith) le_rfl
    have hpos : 0 < cs / 2 * x ^ 2 := mul_pos (by linarith) (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left hm hr]
  constructor
  · intro h
    unfold DRBaseline.estReduction
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · intro h
    unfold DRBaseline.estReduction
    exact max_le (by linarith) hx0
