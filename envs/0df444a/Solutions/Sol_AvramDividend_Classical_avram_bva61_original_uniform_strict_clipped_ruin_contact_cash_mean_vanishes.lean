-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva61_original_uniform_strict_clipped_ruin_contact_cash_mean_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T13:13:41.113554+00:00
-- url     : https://prove2.me/submissions/1379c9b9-5cc0-457e-8ff8-36a963340189

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_contact_tail_expected_vanishes
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (hTpos : 0 < T) :
    Tendsto (fun n : ℕ =>
      ∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal - (T : ℝ) / ((n : ℝ) + 2))
              ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let δ : ℕ → ℝ := fun n => (T : ℝ) / ((n : ℝ) + 2)
  have hTr : 0 < (T : ℝ) := by
    exact_mod_cast hTpos
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    dsimp [δ]
    positivity
  have hδanti : Antitone δ := by
    intro i j hij
    dsimp [δ]
    apply div_le_div_of_nonneg_left (le_of_lt hTr)
    · positivity
    · have hr : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
  have hδrecip :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
        atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
    convert h using 1
    ext n
    apply congrArg (fun z : ℝ => (1 : ℝ) / z)
    push_cast
    ring
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hh : Tendsto
        (fun n : ℕ => (T : ℝ) * ((1 : ℝ) / ((n : ℝ) + 2)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (T : ℝ)) atTop (𝓝 (T : ℝ))).mul hδrecip)
    simpa only [δ, mul_one_div] using hh
  simpa only [δ] using
    (avram_p3_grid3_original_clipped_ruin_contact_tail_expected_vanishes
      X x C D hD q hq T δ hδpos hδanti hδ)
