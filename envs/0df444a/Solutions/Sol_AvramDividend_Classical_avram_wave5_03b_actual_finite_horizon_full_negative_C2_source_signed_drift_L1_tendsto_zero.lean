-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_signed_drift_L1_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:06:04.319588+00:00
-- url     : https://prove2.me/submissions/226456ed-64a0-4308-969c-7d2d6d2602bb

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The signed, source-coupled finite-band Lévy jump drift discarded under
truncation vanishes in original physical time×P L1, without an assumed
independent jump source, stochastic isometry or source compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖∫ z in B n, HS (p,z) ∂X.ν‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
      atTop (𝓝 0) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let physical : Measure (ℝ≥0 × Ω) :=
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P
  change Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
    ‖∫ z in B n, HS (p,z) ∂X.ν‖ₑ ∂physical) atTop (𝓝 0)
  have hTail :
      Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂physical)
        atTop (𝓝 0) :=
    (avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_tendsto_zero
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv T B hBm hBneg hBanti hBempty).1
  have hle (n : ℕ) :
      (∫⁻ p : ℝ≥0 × Ω,
        ‖∫ z in B n, HS (p,z) ∂X.ν‖ₑ ∂physical) ≤
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂physical) := by
    apply lintegral_mono
    intro p
    simpa only [Real.enorm_eq_ofReal_abs] using
      (enorm_integral_le_lintegral_enorm
        (μ := X.ν.restrict (B n)) (fun z : ℝ => HS (p,z)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hTail (fun _ => bot_le) hle
