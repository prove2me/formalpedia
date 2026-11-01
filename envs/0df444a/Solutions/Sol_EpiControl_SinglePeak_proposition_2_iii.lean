-- Prove2me | solution 1 for EpiControl.SinglePeak.proposition_2_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:57:50.375859+00:00
-- url     : https://prove2.me/submissions/5902ab01-994d-4612-94fb-37471a2d90f2

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (η : ℝ → ℝ) (hη : P.IsCostate β s i η)
    (hconv : ∀ t ∈ Icc 0 P.T, P.ArgminAt (gain η s i t) (β t)) :
    ∀ t ∈ Icc 0 P.T, ∀ t' ∈ Icc 0 P.T,
      gain η s i t' < gain η s i t → β t ≤ β t' := by
  intro t ht t' ht' hlt
  obtain ⟨hb, hmin⟩ := hconv t ht
  obtain ⟨hb', hmin'⟩ := hconv t' ht'
  have h1 := hmin (β t') hb'
  have h2 := hmin' (β t) hb
  by_contra hne
  push_neg at hne
  have : (gain η s i t - gain η s i t') * (β t - β t') > 0 :=
    mul_pos (by linarith) (by linarith)
  nlinarith
