-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen10_drift_cancelled_dividend_cap_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:19:00.747649+00:00
-- url     : https://prove2.me/submissions/fea994c3-e16d-4d6b-ad40-09d2e9cb6548

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (b x T : ℝ) (hb : 0 ≤ b)
    (s : Ω → ℝ≥0) (A : Ω → ℝ) (hA : ∀ ω, 0 ≤ A ω)
    (hX : ∀ t ω, X t ω ≤ b * (t : ℝ)) :
    ∀ ω (t : ℝ≥0),
      x + X t ω -
        ((if s ω < t then A ω else 0) + b * max ((t : ℝ) - T) 0)
        ≤ x + b * T := by
  intro ω t
  have ha : (0 : ℝ) ≤ (if s ω < t then A ω else 0) := by
    split_ifs
    · exact hA ω
    · exact le_refl 0
  have hd : (t : ℝ) - T ≤ max ((t : ℝ) - T) 0 := le_max_left _ _
  have hm : b * ((t : ℝ) - T) ≤ b * max ((t : ℝ) - T) 0 :=
    mul_le_mul_of_nonneg_left hd hb
  nlinarith [hX t ω]
