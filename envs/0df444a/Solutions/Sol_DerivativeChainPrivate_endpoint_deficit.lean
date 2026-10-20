-- Prove2me | solution 1 for DerivativeChainPrivate.endpoint_deficit
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T03:08:53.10198+00:00
-- url     : https://prove2.me/submissions/fadd8daf-9e2f-4265-b703-940bfdbb997e

import Mathlib

/- A candidate sorry-free proof script for a finite scalar implication.
   NOT compiled in the preparation environment. Not submitted to Prove2Me.
   This theorem does not assert that derivative towers satisfy its hypotheses. -/
open scoped BigOperators


theorem solution {ι : Type*} [Fintype ι]
    (w D B : ι → ℝ) (C E : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hD : ∀ i, 0 ≤ D i)
    (henergy : (∑ i, w i * (D i) ^ 2) ≤ E)
    (hdeficit : E < ∑ i, w i * (max (C - B i) 0) ^ 2) :
    ∃ i, D i + B i < C := by
  classical
  by_contra h
  push_neg at h
  have hp : ∀ i, (max (C - B i) 0) ^ 2 ≤ (D i) ^ 2 := by
    intro i
    have hs0 : 0 ≤ max (C - B i) 0 := le_max_right _ _
    have hs : max (C - B i) 0 ≤ D i := max_le (by linarith [h i]) (hD i)
    have hm := mul_nonneg (sub_nonneg.mpr hs) (add_nonneg (hD i) hs0)
    nlinarith
  have hsum : (∑ i, w i * (max (C - B i) 0) ^ 2) ≤
      ∑ i, w i * (D i) ^ 2 :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hp i) (hw i))
  linarith


