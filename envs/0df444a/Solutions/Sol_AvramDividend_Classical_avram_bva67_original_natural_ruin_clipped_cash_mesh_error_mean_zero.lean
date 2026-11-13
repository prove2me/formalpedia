-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva67_original_natural_ruin_clipped_cash_mesh_error_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:09:57.727798+00:00
-- url     : https://prove2.me/submissions/fcbbed9f-7148-46da-bd6c-e681afb707cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_natural_ruin_clock_full_stopping_package
import Theorems.Thm_AvramDividend_Classical_avram_bva66_original_strict_stopped_cash_mesh_error_expected_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    :
    let ρ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    (∀ m : ℕ, Integrable (E m) P) ∧
    Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (nhds (0 : ℝ)) := by
  dsimp only
  obtain ⟨hBound, hStop, _⟩ :=
    avram_sweep16_20261106_natural_ruin_clock_full_stopping_package
      X x C D hD n hn
  exact
    avram_bva66_original_strict_stopped_cash_mesh_error_expected_tendsto_zero
      X hX x C D hD q hq n hn
      (fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
      hStop hBound

