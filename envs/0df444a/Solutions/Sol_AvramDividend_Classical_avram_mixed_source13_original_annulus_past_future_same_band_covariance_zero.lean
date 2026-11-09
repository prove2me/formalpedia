-- Prove2me | solution 1 for AvramDividend.Classical.avram_mixed_source13_original_annulus_past_future_same_band_covariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:26:51.547199+00:00
-- url     : https://prove2.me/submissions/d94daef8-2ccc-40b5-b4f4-dee5ab6cbaed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_past_future_borel_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_levy_rate_difference

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A physical negative annulus has centred orthogonal past and later marked counts. -/
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
    Integrable (fun ω => ((A ω).toReal - r) * ((F ω).toReal - q)) P ∧
    (∫ ω, ((A ω).toReal - r) * ((F ω).toReal - q) ∂P) = 0 := by
  classical
  let c : ℝ := -(1 / ((n : ℝ) + 1))
  let d : ℝ := -(1 / ((m : ℝ) + 1))
  let B : Set ℝ := Ioc c d
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
  change Integrable (fun ω => ((A ω).toReal - r) *
      ((F ω).toReal - q)) P ∧
    (∫ ω, ((A ω).toReal - r) * ((F ω).toReal - q) ∂P) = 0
  let ε : ℝ := 1 / ((m : ℝ) + 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hBand : B ⊆ Ioo (-1 : ℝ) (-ε) := by
    intro x hx
    change c < x ∧ x ≤ d at hx
    have hc : -1 ≤ c := by
      dsimp [c]
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith
      have hrec : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
        by simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn)
      linarith
    have hd : d < -ε := by
      dsimp [d, ε]
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hlt : (m : ℝ) + 1 < (m : ℝ) + 2 := by linarith
      have hrec : (1 : ℝ) / ((m : ℝ) + 2) <
          1 / ((m : ℝ) + 1) :=
        one_div_lt_one_div_of_lt hm hlt
      linarith
    exact ⟨lt_of_le_of_lt hc hx.1, lt_of_le_of_lt hx.2 hd⟩
  have hCut : B ⊆ Iic d := by
    intro x hx
    exact hx.2
  have hCov :=
    avram_mixed_source13_original_annulus_past_future_borel_covariance_zero
      X s t hst n m hnm ε hε B measurableSet_Ioc hBand hCut
  let fullRate : ℕ → ℝ := fun i =>
    ((s : ℝ≥0∞) * X.ν (Iic (-(1 / ((i : ℝ) + 1))))).toReal
  have hRate : fullRate m - fullRate n = r := by
    have h := avram_mixed_source13_original_annulus_levy_rate_difference
      X s n m hnm
    change fullRate m = fullRate n + r at h
    linarith
  change Integrable (fun ω =>
      ((A ω).toReal - (fullRate m - fullRate n)) *
        ((F ω).toReal - q)) P ∧
    (∫ ω, ((A ω).toReal - (fullRate m - fullRate n)) *
        ((F ω).toReal - q) ∂P) = 0 at hCov
  rw [hRate] at hCov
  exact hCov