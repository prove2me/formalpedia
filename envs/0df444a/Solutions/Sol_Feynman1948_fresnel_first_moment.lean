-- Prove2me | solution 1 for Feynman1948.fresnel_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T18:24:31.653553+00:00
-- url     : https://prove2.me/submissions/91068b99-b218-4d0d-b8b3-03e48f958a92

import Definitions.Def_Feynman1948_WaveEquation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

open Complex MeasureTheory Feynman1948

theorem solution (ħ m ε : ℝ) (_hħ : 0 < ħ) (_hm : 0 < m) (_hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → regularizedMoment ħ m ε δ 1 = 0 := by
  intro δ hδ
  unfold regularizedMoment
  simp only [pow_one]
  have h := integral_neg_eq_self
    (fun ξ : ℝ => (ξ : ℂ) *
      exp (I * m * (ξ : ℂ) ^ 2 / (2 * (ħ * (1 - I * δ)) * ε))) volume
  simp only [Complex.ofReal_neg, neg_sq, neg_mul] at h
  rw [integral_neg] at h
  apply Complex.ext
  · exact eq_zero_of_neg_eq (congrArg Complex.re h)
  · exact eq_zero_of_neg_eq (congrArg Complex.im h)
