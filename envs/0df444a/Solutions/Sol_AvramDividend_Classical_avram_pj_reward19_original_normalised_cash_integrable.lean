-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward19_original_normalised_cash_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:01:35.46257+00:00
-- url     : https://prove2.me/submissions/943ea358-8dac-4821-96e1-893c202f251d

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_masked_reward_dominates_exact_F
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopped_real_cash_measurable_no_aux

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped inclusive dividend cash is integrable whenever the
zero-clock-normalised physical stopped reward is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Cash : Ω → ℝ := fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let G : Ω → ℝ := fun ω =>
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
            else riskProcess X x D (ρ ω) ω) + Cash ω
    Integrable G P → Integrable Cash P := by
  dsimp only
  intro hGI
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let W : Ω → ℝ := fun ω =>
    if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
    else riskProcess X x D (ρ ω) ω
  let Term : Ω → ℝ := fun ω =>
    Real.exp (-(q * (ρ ω : ℝ))) * w (W ω)
  let F : Ω → ℝ := fun ω => Term ω + Cash ω
  let G : Ω → ℝ := fun ω =>
    if ρ ω = 0 then w x else
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) + Cash ω
  change Integrable G P at hGI
  change Integrable Cash P
  have hTerm : ∀ ω, 0 ≤ Term ω :=
    avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hxc
      D hD q ρ W Term (by intro ω; rfl) (by intro ω; rfl)
  have hCashNonneg (ω : Ω) : 0 ≤ Cash ω := by
    exact ENNReal.toReal_nonneg
  have hFleG (ω : Ω) : F ω ≤ G ω := by
    have hdom :=
      avram_ubv_loc6_original_masked_reward_dominates_exact_F
        X x q w C D hD hjump (fun _ => ρ) (fun _ => F)
        (by intro k η; rfl) 0 ω
    by_cases h0 : ρ ω = 0
    · simpa [G, h0] using hdom
    · simp only [F, Term, W, G, h0, false_or, if_false] at hdom ⊢
      simpa [h0] using hdom
  have hCashLeG (ω : Ω) : Cash ω ≤ G ω := by
    have hCashLeF : Cash ω ≤ F ω := by
      dsimp [F]
      linarith [hTerm ω]
    exact le_trans hCashLeF (hFleG ω)
  have hCashMeas : AEStronglyMeasurable Cash P :=
    avram_wave6_06_original_rightcont_stopped_real_cash_measurable_no_aux
      X x C D hD q ρ hρstop Cash (by intro ω; rfl)
  apply hGI.mono' hCashMeas
  filter_upwards [] with ω
  have hGNonneg : 0 ≤ G ω :=
    le_trans (hCashNonneg ω) (hCashLeG ω)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (hCashNonneg ω), abs_of_nonneg hGNonneg]
    using hCashLeG ω
