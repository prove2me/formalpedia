-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_capped_killed_record_exact_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:40:26.393993+00:00
-- url     : https://prove2.me/submissions/bd3a75da-be4b-4ee3-af43-ea24fbfdb3c4

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_record_no_positive_overshoot
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
     ENNReal.ofReal
       (Real.exp (φ * b - (p + q) * (τ : ℝ)))) := by
  intro τ
  rw [avram_ws01h_capped_record_no_positive_overshoot X b hb N ω hhit,
      hroot]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  rw [← Real.exp_add]
  congr 1
  ring
