-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB41_original_strict_clock_gaussian_caplinear_occupation_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:01:00.896351+00:00
-- url     : https://prove2.me/submissions/641c8b62-14e8-480b-bb7a-277cf55d5b63

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_original_gaussian_caplinear_offkink_integral_drift_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gbB39_original_postpayment_gaussian_exact_level_occupation_zero
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_original_strict_clock_postpaid_real_time_positive_ae
import Theorems.Thm_AvramDividend_Classical_avram_gbB42_original_postpayment_real_time_reserve_measurable_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω t, 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z =>
        if z ≤ b then w z else w b + (z - b)
      Integrable (fun t => X.generator V (Y t) - q * V (Y t))
        (volume.restrict S) →
      Integrable (fun t => if b < Y t then max X.c 0 else 0)
        (volume.restrict S) →
      (∫ t, X.generator V (Y t) - q * V (Y t) ∂(volume.restrict S)) ≤
        (∫ t, if b < Y t then max X.c 0 else 0 ∂(volume.restrict S)) := by
  have hKink :=
    avram_gbB39_original_postpayment_gaussian_exact_level_occupation_zero
      X hBV hν x b D hD n ρ
  filter_upwards [hKink] with ω hNull
  let S : Set ℝ := {t : ℝ |
    0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
  let Y : ℝ → ℝ := fun t =>
    x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
  let V : ℝ → ℝ := fun z =>
    if z ≤ b then w z else w b + (z - b)
  change Integrable (fun t => X.generator V (Y t) - q * V (Y t))
      (volume.restrict S) →
    Integrable (fun t => if b < Y t then max X.c 0 else 0)
      (volume.restrict S) →
    (∫ t, X.generator V (Y t) - q * V (Y t) ∂(volume.restrict S)) ≤
      (∫ t, if b < Y t then max X.c 0 else 0 ∂(volume.restrict S))
  have hSm : MeasurableSet S := by
    dsimp [S]
    measurability
  have hEqMeas : MeasurableSet {t : ℝ | Y t = b} :=
    (measurableSet_singleton b).preimage (avram_gbB42_original_postpayment_real_time_reserve_measurable_path X x D hD ω)
  have hZero : (volume.restrict S) {t : ℝ | Y t = b} = 0 := by
    rw [Measure.restrict_apply hEqMeas]
    have hEq : S ∩ {t : ℝ | Y t = b} =
        {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω = b} := by
      ext t
      simp only [S, Y, Set.mem_inter_iff, Set.mem_setOf_eq]
      tauto
    rw [Set.inter_comm, hEq]
    exact hNull
  have hNoKink : ∀ᵐ t ∂(volume.restrict S), Y t ≠ b :=
    ae_iff.mpr (by simpa only [not_not] using hZero)
  have hPos : ∀ᵐ t ∂(volume.restrict S), 0 < Y t := by
    simpa only [S, Y] using
      avram_gbB40_original_strict_clock_postpaid_real_time_positive_ae
        X x D hD ω (ρ ω) n δ hδ (hFloor ω)
  exact avram_gbB38_original_gaussian_caplinear_offkink_integral_drift_occupation
    X hν w b q hq hwb hHJB (volume.restrict S) Y hPos hNoKink
