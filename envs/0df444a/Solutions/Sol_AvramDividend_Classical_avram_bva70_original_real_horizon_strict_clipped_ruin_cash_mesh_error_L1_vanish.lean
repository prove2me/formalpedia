-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva70_original_real_horizon_strict_clipped_ruin_cash_mesh_error_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:30:58.731697+00:00
-- url     : https://prove2.me/submissions/c52d6b44-53b5-4615-8835-05f6450b8b3d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva69_original_real_horizon_clipped_ruin_NNReal_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_avram_bva66_original_strict_stopped_cash_mesh_error_expected_tendsto_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0)) :
    let ρ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
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
  have hStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : WithTop ℝ≥0)) :=
    avram_bva69_original_real_horizon_clipped_ruin_NNReal_isStoppingTime
      X x C D hD T
  have hBound : ∀ ω : Ω,
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal ≤ (n : ℝ≥0) := by
    intro ω
    have hFinite :
        min (ruinTime X x D ω) (T : ℝ≥0∞) ≠ ⊤ := by
      have hlt : min (ruinTime X x D ω) (T : ℝ≥0∞) < ⊤ :=
        lt_of_le_of_lt (min_le_right _ _) (by simp)
      exact ne_of_lt hlt
    have hLeT : (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal ≤ T := by
      apply (ENNReal.coe_le_coe).mp
      rw [ENNReal.coe_toNNReal hFinite]
      exact min_le_right _ _
    exact le_trans hLeT hT
  exact
    avram_bva66_original_strict_stopped_cash_mesh_error_expected_tendsto_zero
      X hX x C D hD q hq n hn
      (fun ω => (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal)
      hStop hBound

