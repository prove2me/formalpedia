-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_capped_killed_record_esscher_likelihood
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:45:09.868403+00:00
-- url     : https://prove2.me/submissions/759fe903-2622-4708-b3c3-311afbe95c4e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_record_no_positive_overshoot

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0) (ω : Ω)
    (φ q p : ℝ) (hroot : X.ψ φ = q)
    (hhit : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    (let τ : ℝ≥0 :=
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     ENNReal.ofReal (Real.exp (-(p * (τ : ℝ)))) *
       ENNReal.ofReal (Real.exp
         (φ * X.X τ ω - (τ : ℝ) * X.ψ φ)) =
     ENNReal.ofReal (Real.exp (-(p * (τ : ℝ)))) *
       ENNReal.ofReal (Real.exp (φ * b - (τ : ℝ) * q))) := by
  intro τ
  rw [avram_ws01h_capped_record_no_positive_overshoot X b hb N ω hhit,
      hroot]
