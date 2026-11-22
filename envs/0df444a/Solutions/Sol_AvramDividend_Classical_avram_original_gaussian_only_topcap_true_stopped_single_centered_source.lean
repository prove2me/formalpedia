-- Prove2me | solution 1 for AvramDividend.Classical.avram_original_gaussian_only_topcap_true_stopped_single_centered_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:27:21.710943+00:00
-- url     : https://prove2.me/submissions/c5e34d43-9b93-4510-a4d5-df238447a560

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
import Theorems.Thm_AvramDividend_Classical_avram_f6_zero_nu_topcap_masked_signed_source_witness
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original topcap Gaussian stopped payoff and a genuinely centred integrable source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
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
    (hCashI : Integrable Cash P) :
    ∃ Mc : Ω → ℝ,
      Integrable Mc P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + Mc ω)
:= by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨θ, K, hθ, hK, hGrowth⟩ :=
    avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
      X hX hBV hν q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad hTop
  have hBound : ∀ ω, τ ω ≤ (n : ℝ≥0) :=
    (avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ τ hτeq (fun _ => le_rfl)).1
  have hTermNN :=
    avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q τ W Term hW hTerm
  have hTermI :=
    avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
      X C x D hD τ W Term hτmeas hτstop n hBound hW
      w q θ K hθ hK hGrowth hTerm hTermMeas
      (Filter.Eventually.of_forall hTermNN)
  have hFI : ∀ k : ℕ, Integrable (fun ω => Term ω + Cash ω) P :=
    fun _ => hTermI.add hCashI
  have hFsource (k : ℕ) (ω : Ω) :
      Term ω + Cash ω =
        Real.exp (-(q * (τ ω : ℝ))) *
          w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
            then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
            else riskProcess X x D (τ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
    rw [hTerm ω, hCash ω, hW ω]
  obtain ⟨Mc, G, R, hMcI, hMcZero, hG, hR, hMasked⟩ :=
    (avram_f6_zero_nu_topcap_masked_signed_source_witness
      X hX hBV hν q hq w C hC hTop hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI (fun _ : ℕ => τ)
      (fun (_ : ℕ) (ω : Ω) => Term ω + Cash ω)
      (fun _ => hτstop) (fun _ _ => le_rfl) hFsource hFI) 0
  have hAtZero (ω : Ω) (hz : τ ω = 0) :
      Term ω + Cash ω ≤ w x :=
    avram_ubv_loc6_original_zero_clock_exact_physical_F_le
      X x q w C D hD hjump (fun _ : ℕ => τ)
      (fun (_ : ℕ) (η : Ω) => Term η + Cash η)
      hFsource 0 ω hz
  refine ⟨Mc, hMcI, hMcZero, ?_⟩
  filter_upwards [hMasked, hG, hR] with ω hm hg hr
  have hPay : Term ω + Cash ω ≤
      (if τ ω = 0 then w x else Term ω + Cash ω) := by
    split_ifs with hz
    · exact hAtZero ω hz
    · exact le_rfl
  linarith
