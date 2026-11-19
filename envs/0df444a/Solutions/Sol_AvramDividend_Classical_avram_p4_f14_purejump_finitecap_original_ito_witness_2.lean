-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f14_purejump_finitecap_original_ito_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:35:13.7646+00:00
-- url     : https://prove2.me/submissions/abb9c8ae-4269-4f37-983a-f6094f4060ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward25_original_finite_cap_initial_event_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_original_exact_clock_zero_reward_le_initial
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hν : X.ν ≠ 0)
    (hσ0 : X.σ = 0)
    (hFinite : C ≠ ⊤) :
    ∀ k, ∃ (M G H : Ω → ℝ),
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, F k ω ≤ w x + M ω + G ω + H ω) := by
  intro k
  have hMean : (∫ ω, F k ω ∂P) ≤ w x := by
    letI : IsProbabilityMeasure P := X.isProbability
    let G : Ω → ℝ := fun ω =>
      if σ k ω = 0 then w x else F k ω
    have hGint : Integrable G P := by
      exact avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
        (𝓕 := 𝓕) (σ k) (hσstop k) (F k) (hFI k) (w x)
    have hGdef : ∀ ω, G ω =
        if σ k ω = 0 then w x else
          Real.exp (-(q * (σ k ω : ℝ))) *
            w (if (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
            else riskProcess X x D (σ k ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal := by
      intro ω
      by_cases hz : σ k ω = 0
      · simp [G, hz]
      · simp [G, hz, hFsource k ω]
    have hBudget : (∫ ω, G ω ∂P) ≤ w x := by
      have hevent :=
        avram_pj_reward25_original_finite_cap_initial_event_budget
          X hX hBV hσ0 q hq w C hC hFinite hw0 hw_cont
          hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD
          hw_nonneg hjump n hn τ hτeq hτmeas hτstop
          (σ k) (hσstop k) (hσle k)
          G hGdef hGint Set.univ MeasurableSet.univ
      simpa using hevent
    have hComp : ∀ᵐ ω ∂P, F k ω ≤ G ω := by
      filter_upwards [] with ω
      by_cases hz : σ k ω = 0
      · simpa [G, hz] using
          (avram_p4_f8_original_exact_clock_zero_reward_le_initial
            X x q w C D hD hjump σ F hFsource k ω hz)
      · simp [G, hz]
    exact (integral_mono_ae (hFI k) hGint hComp).trans hBudget
  have hWitness :=
    avram_p4_f_assembly_expected_budget_witness_of_original_L1
      X w x (F k) (fun _ : Ω => (0 : ℝ)) (hFI k) (by fun_prop)
      (by simpa using hMean)
  simpa using hWitness
