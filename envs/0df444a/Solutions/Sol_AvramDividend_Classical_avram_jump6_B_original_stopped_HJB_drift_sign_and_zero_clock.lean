-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_stopped_HJB_drift_sign_and_zero_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:00:50.465725+00:00
-- url     : https://prove2.me/submissions/b66190aa-59a7-48df-a702-22efdb8e7852

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0)
    (μ : Measure ℝ≥0) (hμ0 : μ {(0 : ℝ≥0)} = 0) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t
    let G : Ω → ℝ := fun ω => ∫ t : ℝ≥0,
      if 0 < Y t ω ∧ ENNReal.ofReal (Y t ω) < C ∧ t ≤ σ ω then
        Real.exp (-(q * (t : ℝ))) *
          (X.generator w (Y t ω) - q * w (Y t ω))
      else 0 ∂μ
    ∀ ω, G ω ≤ 0 ∧ (σ ω = 0 → G ω = 0) := by
  intro Y G ω
  constructor
  · apply integral_nonpos_of_ae
    filter_upwards [] with t
    split_ifs with h
    · exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (Real.exp_pos _)) (hw_gen (Y t ω) h.1 h.2.1).2
    · exact le_refl 0
  · intro hz
    have hNotZero : ∀ᵐ t : ℝ≥0 ∂μ, t ≠ 0 := by
      apply ae_iff.mpr
      simpa using hμ0
    apply integral_eq_zero_of_ae
    filter_upwards [hNotZero] with t ht
    split_ifs with h
    · have htzero : t = 0 :=
        le_antisymm (by simpa only [hz] using h.2.2) (by exact zero_le)
      exact False.elim (ht htzero)
    · rfl
