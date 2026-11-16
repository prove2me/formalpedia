-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54cp_original_stopped_real_time_generator_drift_upperstrip_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:20:44.636756+00:00
-- url     : https://prove2.me/submissions/03a40813-c1ed-4cb0-aeb8-0a7bd2244ad3

import Theorems.Thm_AvramDividend_Classical_avram_gbB39_original_postpayment_gaussian_exact_level_occupation_zero
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_original_strict_clock_postpaid_real_time_positive_ae
import Theorems.Thm_AvramDividend_Classical_avram_gbB42_original_postpayment_real_time_reserve_measurable_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_original_gaussian_caplinear_offkink_integral_drift_occupation
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (b : ℝ)
    (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let μ : Measure ℝ := volume.restrict S
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
      Integrable (fun t => X.generator V (Y t) - q * V (Y t)) μ →
      Integrable (fun t => if b < Y t then max X.c 0 else 0) μ →
      (∫ t, X.generator V (Y t) - q * V (Y t) ∂μ) ≤
        (∫ t, if b < Y t then max X.c 0 else 0 ∂μ) := by
  classical
  have hNull :=
    avram_gbB39_original_postpayment_gaussian_exact_level_occupation_zero
      X hBV hν x b D hD n ρ
  filter_upwards [hNull] with ω hω
  intro S μ Y V hGenI hStripI
  have hPos : ∀ᵐ t ∂μ, 0 < Y t := by
    simpa only [S, μ, Y] using
      (avram_gbB40_original_strict_clock_postpaid_real_time_positive_ae
        X x D hD ω (ρ ω) n δ hδ (hFloor ω))
  have hYmeas : Measurable Y := by
    simpa only [Y] using
      (avram_gbB42_original_postpayment_real_time_reserve_measurable_path
        X x D hD ω)
  have hLevelMeas : MeasurableSet {t : ℝ | Y t = b} :=
    measurableSet_eq_fun hYmeas measurable_const
  have hLevelSet : {t : ℝ | Y t = b} ∩ S =
      {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = b} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, S, Y]
    tauto
  have hLevelZero : μ {t : ℝ | Y t = b} = 0 := by
    change (volume.restrict S) {t : ℝ | Y t = b} = 0
    rw [Measure.restrict_apply hLevelMeas, hLevelSet]
    exact hω
  have hNoKink : ∀ᵐ t ∂μ, Y t ≠ b :=
    (ae_iff).2 (by simpa only [not_not] using hLevelZero)
  exact
    avram_gbB38_original_gaussian_caplinear_offkink_integral_drift_occupation
      X hν w b q hq hwb hHJB μ Y hPos hNoKink hGenI hStripI
