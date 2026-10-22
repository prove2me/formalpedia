-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_negative_jump_integral_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:20:59.483858+00:00
-- url     : https://prove2.me/submissions/cc6b8633-c2ed-4494-b315-1fa82c845967

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Negation transports real jump integrals from negative jumps to
positive jump magnitudes, with exact half-line restrictions. -/
theorem solution (ν : Measure ℝ) (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ y in Iio (0 : ℝ), F (-y) ∂ν) =
      ∫ z in Ioi (0 : ℝ),
        F z ∂(ν.map (fun y : ℝ => -y)) := by
  let n : ℝ → ℝ := fun y => -y
  have hn : Measurable n := measurable_id.neg
  have hpre : n ⁻¹' Ioi (0 : ℝ) = Iio (0 : ℝ) := by
    ext y
    simp only [mem_preimage, mem_Ioi, mem_Iio, n]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  have hrestrict :
      (ν.map n).restrict (Ioi (0 : ℝ)) =
        (ν.restrict (Iio (0 : ℝ))).map n := by
    rw [Measure.restrict_map hn measurableSet_Ioi]
    rw [hpre]
  have hFm : AEStronglyMeasurable F
      ((ν.restrict (Iio (0 : ℝ))).map n) :=
    hF.aestronglyMeasurable
  change (∫ y : ℝ, F (n y) ∂ν.restrict (Iio (0 : ℝ))) =
    ∫ z : ℝ, F z ∂(ν.map n).restrict (Ioi (0 : ℝ))
  rw [hrestrict]
  exact (integral_map hn.aemeasurable hFm).symm
