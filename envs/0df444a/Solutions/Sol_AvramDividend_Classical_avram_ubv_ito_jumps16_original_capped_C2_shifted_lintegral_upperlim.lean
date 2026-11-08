-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps16_original_capped_C2_shifted_lintegral_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:20:57.181369+00:00
-- url     : https://prove2.me/submissions/80bf5369-ce2d-4091-906c-57772e7438a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_real_upperlim_ofReal
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_shifted_lintegral_upperlim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original Levy measure inherits the negative-mark one-sided
upper bound even across a ruin-contact atom, after adding the integrable
quadratic envelope. This is the measure-valued precursor to signed reverse
Fatou in the original-process Itô–Meyer argument. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) c)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y))
    (h : ℝ → ℝ) (hhmeas : Measurable h)
    (hh_nonneg : ∀ z : ℝ, 0 ≤ h z)
    (hhfinite : (∫⁻ z, ENNReal.ofReal (2 * h z) ∂X.ν) ≠ ⊤)
    (hneg_ae : ∀ᵐ z ∂X.ν, z < 0)
    (hfmeas : ∀ n : ℕ, Measurable (fun z : ℝ =>
      w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0)))
    (habs : ∀ (n : ℕ) (z : ℝ),
      |w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0)| ≤ h z) :
    let R : ℝ → ℝ → ℝ := fun a z =>
      w (a + z) - w a -
        (if -1 < z then z * deriv w a else 0)
    Filter.limsup (fun n : ℕ =>
      ∫⁻ z, ENNReal.ofReal (h z + R (u n) z) ∂X.ν) atTop ≤
      ∫⁻ z, ENNReal.ofReal (h z + R y z) ∂X.ν := by
  intro R
  have hpoint : ∀ᵐ z ∂X.ν,
      Filter.limsup (fun n : ℕ => ENNReal.ofReal (h z + R (u n) z)) atTop ≤
        ENNReal.ofReal (h z + R y z) := by
    filter_upwards [hneg_ae] with z hz
    apply avram_ubv_ito_jumps16_real_upperlim_ofReal
    intro ε hε
    simpa only [R] using
      (avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
        w cap c hc hcCap hw_smooth hw0 hwcont hwneg
        y z hy hz u hu ε hε)
  exact avram_ubv_ito_jumps16_original_shifted_lintegral_upperlim
    X h hhmeas hh_nonneg hhfinite
    (fun n z => R (u n) z) (R y) hfmeas habs hpoint
