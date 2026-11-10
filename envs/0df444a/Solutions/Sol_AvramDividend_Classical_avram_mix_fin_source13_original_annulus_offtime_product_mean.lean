-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin_source13_original_annulus_offtime_product_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:37:47.747854+00:00
-- url     : https://prove2.me/submissions/862abcc4-beb9-4617-8336-13c074363c59

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_past_future_same_band_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original off-time annulus count product has its true compensator product mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ B)
    let F : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := ((s : ℝ≥0∞) * X.ν B).toReal
    let q : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (A ω).toReal * (F ω).toReal) P ∧
      (∫ ω, (A ω).toReal * (F ω).toReal ∂P) = r * q := by
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let A : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 s ×ˢ B)
  let F : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let r : ℝ := ((s : ℝ≥0∞) * X.ν B).toReal
  let q : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => (A ω).toReal * (F ω).toReal) P ∧
    (∫ ω, (A ω).toReal * (F ω).toReal ∂P) = r * q
  have hCov :=
    avram_mixed_source13_original_annulus_past_future_same_band_covariance_zero
      X s t hst n m hnm
  change Integrable (fun ω => ((A ω).toReal - r) * ((F ω).toReal - q)) P ∧
    (∫ ω, ((A ω).toReal - r) * ((F ω).toReal - q) ∂P) = 0 at hCov
  have hB : MeasurableSet B := measurableSet_Ioc
  have hSep : B ⊆ Iic (-(1 / ((m : ℝ) + 1))) := by
    intro z hz
    exact hz.2
  have hε : 0 < (1 / ((m : ℝ) + 1)) := by positivity
  have hA :=
    avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto
      X 0 s (show (0 : ℝ≥0) ≤ s from zero_le) B hB _ hε hSep
  change Integrable (fun ω => (A ω).toReal -
      (((s - 0 : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) P ∧
    (∫ ω, (A ω).toReal -
      (((s - 0 : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal ∂P) = 0 at hA
  simp only [tsub_zero] at hA
  have hF :=
    avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto
      X s t hst B hB _ hε hSep
  change Integrable (fun ω => (F ω).toReal - q) P ∧
    (∫ ω, (F ω).toReal - q ∂P) = 0 at hF
  have hAr : Integrable (fun ω => q * ((A ω).toReal - r)) P :=
    hA.1.const_mul q
  have hFr : Integrable (fun ω => r * ((F ω).toReal - q)) P :=
    hF.1.const_mul r
  have h1 : Integrable (fun ω =>
      ((A ω).toReal - r) * ((F ω).toReal - q) +
        r * ((F ω).toReal - q)) P := hCov.1.add hFr
  have h2 : Integrable (fun ω =>
      (((A ω).toReal - r) * ((F ω).toReal - q) +
        r * ((F ω).toReal - q)) +
        q * ((A ω).toReal - r)) P := h1.add hAr
  have hEq :
      (fun ω => (A ω).toReal * (F ω).toReal) =
      (fun ω =>
        (((A ω).toReal - r) * ((F ω).toReal - q) +
          r * ((F ω).toReal - q)) +
          q * ((A ω).toReal - r) + r * q) := by
    funext ω
    ring
  rw [hEq]
  constructor
  · exact h2.add (integrable_const _)
  · calc
      (∫ ω, (((A ω).toReal - r) * ((F ω).toReal - q) +
          r * ((F ω).toReal - q)) +
          q * ((A ω).toReal - r) + r * q ∂P) =
          (∫ ω, ((A ω).toReal - r) * ((F ω).toReal - q) ∂P) +
          (∫ ω, r * ((F ω).toReal - q) ∂P) +
          (∫ ω, q * ((A ω).toReal - r) ∂P) +
          (∫ _ : Ω, (r * q : ℝ) ∂P) := by
            rw [integral_add h2 (integrable_const _),
                integral_add h1 hAr, integral_add hCov.1 hFr]
      _ = 0 + r * 0 + q * 0 + r * q := by
          rw [integral_const_mul, integral_const_mul,
              hCov.2, hF.2, hA.2]
          simp
      _ = r * q := by ring