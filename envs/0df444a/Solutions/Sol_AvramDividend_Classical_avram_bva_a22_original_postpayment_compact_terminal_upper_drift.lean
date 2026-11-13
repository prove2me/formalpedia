-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_postpayment_compact_terminal_upper_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:11:21.41773+00:00
-- url     : https://prove2.me/submissions/341fa852-3606-4ef9-a5c6-5867f51d97cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (c d L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d,
      w z - w y ≤ L * max (z - y) 0) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (x + X.X s ω - rightLimit D s ω) ∈ Icc c d →
      (x + X.X t ω - rightLimit D t ω) ∈ Icc c d →
      w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X s ω - rightLimit D s ω) ≤
      L * (((t : ℝ) - (s : ℝ)) * max X.drift 0) := by
  filter_upwards
    [avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
      X hBV x D hD] with ω hω
  intro s t hst hs ht
  have hΔ : 0 ≤ (t : ℝ) - (s : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hst)
  have hUpper :
      (x + X.X t ω - rightLimit D t ω) -
        (x + X.X s ω - rightLimit D s ω) ≤
      ((t : ℝ) - (s : ℝ)) * X.drift :=
    hω s t hst
  have hProd :
      ((t : ℝ) - (s : ℝ)) * X.drift ≤
      ((t : ℝ) - (s : ℝ)) * max X.drift 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hΔ
  have hNonneg :
      0 ≤ ((t : ℝ) - (s : ℝ)) * max X.drift 0 :=
    mul_nonneg hΔ (le_max_right _ _)
  have hMax :
      max ((x + X.X t ω - rightLimit D t ω) -
        (x + X.X s ω - rightLimit D s ω)) 0 ≤
        ((t : ℝ) - (s : ℝ)) * max X.drift 0 :=
    max_le (hUpper.trans hProd) hNonneg
  exact (hLip _ hs _ ht).trans
    (mul_le_mul_of_nonneg_left hMax hL)
