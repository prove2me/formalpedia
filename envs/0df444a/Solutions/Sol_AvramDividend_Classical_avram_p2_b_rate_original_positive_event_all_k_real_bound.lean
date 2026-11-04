-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_positive_event_all_k_real_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:58:57.694428+00:00
-- url     : https://prove2.me/submissions/10f66ac4-14a8-49d8-94ec-ed87cafc0b8c

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_each_high_moment_eventually_zero_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_positive_increment_weighted_markov
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_ennreal_product_toReal_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 1 < R) (k : ℕ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      R ^ k * ((R - 1) ^ 4 * ((P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)}).toReal / h)) ≤
      (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1 := by
  let C : ℝ := (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1
  have hν : 0 ≤
      ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν :=
    integral_nonneg (fun y => by positivity)
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hbound :=
    AvramDividend.Classical.avram_p2_b_rate_original_each_high_moment_eventually_zero_bound
      X θ hθ k
  have hp : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < h := by
    change Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Ioi 0)
    exact self_mem_nhdsWithin
  filter_upwards [hbound, hp] with h hh hpos
  have hInt :=
    AvramDividend.Classical.avram_p2_b_rate_original_weighted_integer_integrable
      X (Real.toNNReal h) k θ hθ
  have hMarkov :=
    AvramDividend.Classical.avram_p2_b_rate_positive_increment_weighted_markov
      P (X.X (Real.toNNReal h)) (hX _) θ R hR k hInt
  have hinput :
      (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
        (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) ≤ h * C := by
    have hmul :
        (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
          (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) < C * h :=
      (div_lt_iff₀ hpos).mp hh
    nlinarith [hmul]
  have hraw :
      ENNReal.ofReal (R ^ k * (R - 1) ^ 4) *
        P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)} ≤
      ENNReal.ofReal (h * C) :=
    hMarkov.trans (ENNReal.ofReal_le_ofReal hinput)
  have hreal :=
    AvramDividend.Classical.avram_p2_b_rate_ennreal_product_toReal_bound
      (R ^ k * (R - 1) ^ 4) (h * C)
      (P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)})
      (by positivity) (mul_nonneg (le_of_lt hpos) hC) hraw
  change R ^ k * ((R - 1) ^ 4 * ((P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)}).toReal / h)) ≤ C
  calc
    _ = ((R ^ k * (R - 1) ^ 4) * (P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)}).toReal) / h := by ring
    _ ≤ (h * C) / h :=
      div_le_div_of_nonneg_right hreal (le_of_lt hpos)
    _ = C := by field_simp [ne_of_gt hpos]
