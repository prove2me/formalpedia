-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn16_original_last_cell_closed_cash_toReal_splits_endpoint_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:31:17.294328+00:00
-- url     : https://prove2.me/submissions/8cac27c8-7bb8-487b-a109-66b705cf354e

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original finite-grid Stieltjes cash in real values retains the right endpoint atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (a : ℝ) (ha : a < (T : ℝ))
    (hStrictFinite :
      (∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤)
    (hAtomFinite :
      (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤) :
    (∫⁻ t in paymentTimes σ ∩ Ioc a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hSplit :=
    avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom
      D hD ω σ T q a ha
  rw [hSplit]
  exact ENNReal.toReal_add hStrictFinite hAtomFinite
