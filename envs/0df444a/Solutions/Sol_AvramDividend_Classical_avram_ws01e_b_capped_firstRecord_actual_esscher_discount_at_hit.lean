-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_actual_esscher_discount_at_hit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:27:55.821134+00:00
-- url     : https://prove2.me/submissions/b369ba54-ba2c-41ef-82be-ceb77064c55b

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- At a genuinely attained uncensored strict record, stopped Esscher
likelihood times residual survival equals the explicit barrier discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (θ p : ℝ) (τ : Ω → ℝ≥0)
    (hτdef : τ = fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
    (ω : Ω)
    (hA : twoSidedExitUpTime X b ω < (N : ℝ≥0∞)) :
    ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
      ENNReal.ofReal (Real.exp
        (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) =
      ENNReal.ofReal (Real.exp
        (θ * b - (p + X.ψ θ) * (τ ω : ℝ))) := by
  have hfinite : twoSidedExitUpTime X b ω ≠ ⊤ := by
    intro ht
    rw [ht] at hA
    exact (not_lt_of_ge le_top) hA
  have hτhit : (τ ω : ℝ≥0∞) = twoSidedExitUpTime X b ω := by
    rw [hτdef]
    change (((min (twoSidedExitUpTime X b ω)
      (N : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) =
        twoSidedExitUpTime X b ω
    rw [min_eq_left (le_of_lt hA)]
    exact ENNReal.coe_toNNReal hfinite
  have hτinf :
      (τ ω : ℝ≥0∞) =
        (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)) := by
    simpa only [twoSidedExitUpTime] using hτhit
  have hhit : X.X (τ ω) ω = b :=
    firstUpcrossing_value_eq_threshold X b hb ω (τ ω) hτinf
  rw [hhit, ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
  rw [← Real.exp_add]
  congr 1
  ring
