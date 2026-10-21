-- Prove2me | solution 1 for AvramDividend.Classical.discounted_postPayment_candidate_grid_exit_integrable_finite_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:17:38.179994+00:00
-- url     : https://prove2.me/submissions/d87b4f17-a509-47d6-93ca-423fd67822b4

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_grid_exit_stopped_measurable
import Theorems.Thm_AvramDividend_Classical_capped_postPayment_candidate_uniform_upper_bound_finite_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_postPayment_terminal_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (x c : ℝ) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max
        (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω -
          rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    Integrable (fun ω =>
      Real.exp (-(q * (clock (K ω) : ℝ))) *
        w (x + X.X (clock (K ω)) ω -
          rightLimit D (clock (K ω)) ω)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hmeas : Measurable (fun ω =>
      Real.exp (-(q * (clock (K ω) : ℝ))) *
        w (x + X.X (clock (K ω)) ω -
          rightLimit D (clock (K ω)) ω)) :=
    discounted_postPayment_candidate_grid_exit_stopped_measurable
      X x D hD.1.1 w hw_cont hw_neg q
      clock H hH lower upper m K hK
  obtain ⟨B, hB0, hB⟩ :=
    capped_postPayment_candidate_uniform_upper_bound_finite_cap
      X x c hc D hD hxc w hw_cont hw_neg
  apply Integrable.of_mem_Icc 0 B hmeas.aemeasurable
  filter_upwards [] with ω
  have hW0 : 0 ≤ w (x + X.X (clock (K ω)) ω -
      rightLimit D (clock (K ω)) ω) :=
    local_verification_postPayment_terminal_nonnegative
      X q w (ENNReal.ofReal c)
      hw_cont hw0 hw_neg hw_smooth hw_hjb
      x hxc D hD ω (clock (K ω))
  have hWB : w (x + X.X (clock (K ω)) ω -
      rightLimit D (clock (K ω)) ω) ≤ B :=
    hB ω (clock (K ω))
  have ht : 0 ≤ (clock (K ω) : ℝ) :=
    NNReal.coe_nonneg _
  have hqt : 0 ≤ q * (clock (K ω) : ℝ) :=
    mul_nonneg hq.le ht
  have hExp : Real.exp (-(q * (clock (K ω) : ℝ))) ≤ 1 := by
    have hle : -(q * (clock (K ω) : ℝ)) ≤ 0 :=
      neg_nonpos.mpr hqt
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
  have hExp0 : 0 ≤ Real.exp (-(q * (clock (K ω) : ℝ))) :=
    (Real.exp_pos _).le
  exact ⟨mul_nonneg hExp0 hW0,
    (mul_le_mul_of_nonneg_right hExp hW0).trans
      (by simpa only [one_mul] using hWB)⟩
