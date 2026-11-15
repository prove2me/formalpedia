-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB38_original_gaussian_caplinear_offkink_integral_drift_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:45:40.737197+00:00
-- url     : https://prove2.me/submissions/4435480f-8862-4f28-b646-684f9b6639ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB35_original_gaussian_caplinear_offkink_HJB_drift_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (w : ℝ → ℝ) (b q : ℝ) (hq : 0 ≤ q) (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0)
    (μ : Measure ℝ) (Y : ℝ → ℝ)
    (hPos : ∀ᵐ t ∂μ, 0 < Y t)
    (hNoKink : ∀ᵐ t ∂μ, Y t ≠ b) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    Integrable (fun t => X.generator V (Y t) - q * V (Y t)) μ →
    Integrable (fun t => if b < Y t then max X.c 0 else 0) μ →
    (∫ t, X.generator V (Y t) - q * V (Y t) ∂μ) ≤
      (∫ t, if b < Y t then max X.c 0 else 0 ∂μ) := by
  let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
  change
    Integrable (fun t => X.generator V (Y t) - q * V (Y t)) μ →
    Integrable (fun t => if b < Y t then max X.c 0 else 0) μ →
    (∫ t, X.generator V (Y t) - q * V (Y t) ∂μ) ≤
      (∫ t, if b < Y t then max X.c 0 else 0 ∂μ)
  intro hInt hOccI
  apply integral_mono_ae hInt hOccI
  filter_upwards [hPos, hNoKink] with t ht hn
  simpa only [V] using
    (avram_gbB35_original_gaussian_caplinear_offkink_HJB_drift_envelope
      X hν w b q hq hwb hHJB (Y t) ht hn)
