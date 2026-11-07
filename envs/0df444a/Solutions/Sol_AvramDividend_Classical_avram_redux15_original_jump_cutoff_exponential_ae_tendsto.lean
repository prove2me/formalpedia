-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux15_original_jump_cutoff_exponential_ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T11:52:04.30942+00:00
-- url     : https://prove2.me/submissions/b86095c1-747a-497b-93f7-f598c4e6936e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_redux16_finite_ennreal_real_cutoff_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Original BV jump cutoff exponential convergence from a finite-series limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ n : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal))) atTop
        (𝓝 (Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)))) := by
  intro n
  filter_upwards [avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top X hBV]
    with ω hω
  let J : ℝ≥0 → ℝ := fun v =>
    Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
  let f : ℝ≥0 → ℝ≥0∞ := fun v =>
    if 0 < v ∧ v ≤ (n : ℝ≥0) then ENNReal.ofReal (J v) else 0
  have hfin : (∑' v : ℝ≥0, f v) < ⊤ := by
    simpa only [f, J] using hω 0 n (by simp)
  have hmask (k : ℕ) :
      (∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧ (1 / ((k : ℝ) + 1)) < J v
        then ENNReal.ofReal (J v) else 0) =
      (∑' v : ℝ≥0,
        if ENNReal.ofReal (1 / ((k : ℝ) + 1)) < f v then f v else 0) := by
    apply tsum_congr
    intro v
    have hp : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    have hiff : (ENNReal.ofReal (1 / ((k : ℝ) + 1)) <
        ENNReal.ofReal (J v)) ↔ (1 / ((k : ℝ) + 1)) < J v :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp
    by_cases ht : 0 < v ∧ v ≤ (n : ℝ≥0)
    · by_cases hc : (1 / ((k : ℝ) + 1)) < J v
      · have he : ENNReal.ofReal (1 / ((k : ℝ) + 1)) <
          ENNReal.ofReal (J v) := hiff.mpr hc
        have hl : 0 < v ∧ v ≤ (n : ℝ≥0) ∧
            (1 / ((k : ℝ) + 1)) < J v := ⟨ht.1, ht.2, hc⟩
        have hr : ENNReal.ofReal (1 / ((k : ℝ) + 1)) < f v := by
          simpa only [f, if_pos ht] using he
        simp only [if_pos hl, f, if_pos ht, if_pos he]
      · have he : ¬(ENNReal.ofReal (1 / ((k : ℝ) + 1)) <
          ENNReal.ofReal (J v)) := fun h => hc (hiff.mp h)
        have hl : ¬(0 < v ∧ v ≤ (n : ℝ≥0) ∧
            (1 / ((k : ℝ) + 1)) < J v) := fun h => hc h.2.2
        have hr : ¬(ENNReal.ofReal (1 / ((k : ℝ) + 1)) < f v) := by
          simpa only [f, if_pos ht] using he
        simp only [if_neg hl, if_neg hr]
    · have hc : ¬(0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < J v) := fun h => ht ⟨h.1, h.2.1⟩
      have hr : ¬(ENNReal.ofReal (1 / ((k : ℝ) + 1)) < f v) := by
        simp [f, ht]
      simp only [if_neg hc, if_neg hr]
  have hlim := avram_redux16_finite_ennreal_real_cutoff_tendsto f hfin
  have hlim' :
      Tendsto (fun k : ℕ =>
        (∑' v : ℝ≥0,
          if 0 < v ∧ v ≤ (n : ℝ≥0) ∧ (1 / ((k : ℝ) + 1)) < J v
          then ENNReal.ofReal (J v) else 0).toReal)
        atTop (𝓝 ((∑' v : ℝ≥0, f v).toReal)) := by
    simpa only [← hmask] using hlim
  simpa [J, f, Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp hlim'.neg
