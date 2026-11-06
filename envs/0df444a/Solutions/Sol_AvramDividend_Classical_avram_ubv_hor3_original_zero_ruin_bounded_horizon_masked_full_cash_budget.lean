-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_full_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:08:10.943528+00:00
-- url     : https://prove2.me/submissions/ceba8774-5f32-40ce-b79c-47746f9862d3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_masked_full_stieltjes_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    (∫⁻ ω, if τ ω = 0 then
      (∫⁻ s in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, if τ ω = 0 then ENNReal.ofReal (w x) else 0 ∂P) := by
  have hMasked :
      (∫⁻ ω, if τ ω = 0 then
        (∫⁻ s in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
        else 0 ∂P) =
      (∫⁻ ω, if τ ω = 0 then
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
        else 0 ∂P) := by
    apply lintegral_congr
    intro ω
    by_cases hZero : τ ω = 0
    · simp only [if_pos hZero]
      have hRuinZero : ruinTime X x D ω = 0 := by
        apply (avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
          X x D n hn ω).mp
        simpa only [hτeq ω] using hZero
      have hClippedZero :
          min (ruinTime X x D ω) (n : ℝ≥0∞) = 0 := by
        simp [hRuinZero]
      have hDomain :
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T =
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (0 : ℝ) := by
        rw [hClippedZero]
        ext s
        constructor
        · intro hs
          have hsZero : s = 0 := by
            rcases hs.1 with ⟨_, hcases⟩
            rcases hcases with hz | hlt
            · exact hz
            · exact False.elim ((not_lt_of_ge bot_le) hlt)
          subst s
          simp [paymentTimes]
        · intro hs
          exact ⟨hs.1, hs.2.trans hT⟩
      rw [hDomain, hZero, hRuinZero]
      simp
    · simp [hZero]
  rw [hMasked]
  exact avram_ubv_hor3_original_zero_clock_masked_full_stieltjes_bound
    X x q w C hw0 hw_cont hw_neg hw_smooth hw_grad hxc
    D hD hjump τ W Cash Term hW hCash hTerm
