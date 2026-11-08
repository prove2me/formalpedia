-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_stieltjes10_original_all_grid_prepayment_with_initial_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:44:25.54451+00:00
-- url     : https://prove2.me/submissions/827d403c-7e49-4378-b0bd-adabd6c27380

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_countable_positive_grid_prejump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original prepayment reserve at all sampled times, with the correct
time-zero right-dividend atom subtracted from the sampled right path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n,
      Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n) =
        riskProcess X x D (u n) ω -
          (if u n = 0 then rightLimit D 0 ω - D 0 ω else 0) := by
  let v : ℕ → ℝ≥0 := fun n => if u n = 0 then 1 else u n
  have hv : ∀ n, 0 < v n := by
    intro n
    by_cases h : u n = 0
    · simp [v, h]
    · have hp : 0 < u n := pos_iff_ne_zero.mpr h
      simpa [v, h] using hp
  filter_upwards
    [avram_bv_stieltjes10_original_countable_positive_grid_prejump
      X x D hD v hv] with ω hpositive
  intro n
  by_cases h : u n = 0
  · simp only [h, ↓reduceIte]
    have hzero : IsBot (0 : ℝ≥0) := by
      simpa only [bot_eq_zero] using (isBot_bot : IsBot (⊥ : ℝ≥0))
    rw [leftLim_eq_of_isBot hzero]
    simp only [riskProcess, X.X_zero]
    ring
  · have hval : v n = u n := by simp [v, h]
    have hp := hpositive n
    rw [hval] at hp
    simpa only [if_neg h, sub_zero] using hp
