-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f7_finite_cap_integrable_clock_expected_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:54:42.488197+00:00
-- url     : https://prove2.me/submissions/985dacab-3bd9-4b37-8e5e-2edb65e2a7de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_gaussian_masked_expected_finitecap
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_purejump_unbounded_variation_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_mixed_gaussian_negativejump_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_masked_reward_dominates_exact_F
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable

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
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P) (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
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
    (hFI : ∀ k, Integrable (F k) P) (hfinite : C ≠ ⊤) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  have hdom (ω : Ω) :
      F k ω ≤ (if σ k ω = 0 then w x else F k ω) :=
    avram_ubv_loc6_original_masked_reward_dominates_exact_F
      X x q w C D hD hjump σ F hFsource k ω
  have hfinish (Mc Ms Ml G R : Ω → ℝ)
      (hMc : Integrable Mc P) (hMs : Integrable Ms P)
      (hMl : Integrable Ml P)
      (hMc0 : (∫ ω, Mc ω ∂P) = 0)
      (hMs0 : (∫ ω, Ms ω ∂P) = 0)
      (hMl0 : (∫ ω, Ml ω ∂P) = 0)
      (hG : ∀ᵐ ω ∂P, G ω ≤ 0)
      (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
      (hbd : ∀ᵐ ω ∂P,
        (if σ k ω = 0 then w x else F k ω) ≤
          w x + Mc ω + Ms ω + Ml ω + G ω + R ω) :
      (∫ ω, F k ω ∂P) ≤ w x := by
    have hConst : Integrable (fun _ : Ω => w x) P :=
      integrable_const (w x)
    have hAll : Integrable (fun ω => w x + Mc ω + Ms ω + Ml ω) P :=
      ((hConst.add hMc).add hMs).add hMl
    have hbdF : ∀ᵐ ω ∂P,
        F k ω ≤ w x + Mc ω + Ms ω + Ml ω := by
      filter_upwards [hG, hR, hbd] with ω hGw hRw hbw
      have hFle := hdom ω
      linarith
    have hMono : (∫ ω, F k ω ∂P) ≤ (∫ ω, w x + Mc ω + Ms ω + Ml ω ∂P) :=
      integral_mono_ae (hFI k) hAll hbdF
    have hEval : (∫ ω, w x + Mc ω + Ms ω + Ml ω ∂P) = w x := by
      calc
        (∫ ω, w x + Mc ω + Ms ω + Ml ω ∂P) =
            (∫ ω, w x + Mc ω + Ms ω ∂P) + (∫ ω, Ml ω ∂P) := by
              simpa only [Pi.add_apply] using
                (integral_add ((hConst.add hMc).add hMs) hMl)
        _ = ((∫ ω, w x + Mc ω ∂P) + (∫ ω, Ms ω ∂P)) +
              (∫ ω, Ml ω ∂P) := by
                simpa only [Pi.add_apply] using
                  congrArg (fun z : ℝ => z + (∫ ω, Ml ω ∂P))
                    (integral_add (hConst.add hMc) hMs)
        _ = (((∫ ω, w x ∂P) + (∫ ω, Mc ω ∂P)) +
              (∫ ω, Ms ω ∂P)) + (∫ ω, Ml ω ∂P) := by
                simpa only [Pi.add_apply] using
                  congrArg (fun z : ℝ => (z + (∫ ω, Ms ω ∂P)) +
                    (∫ ω, Ml ω ∂P)) (integral_add hConst hMc)
        _ = w x := by simp [hMc0, hMs0, hMl0]
    exact hMono.trans_eq hEval
  by_cases hν : X.ν = 0
  · have hσ : X.σ ≠ 0 := by
      intro hs
      apply hBV
      refine ⟨hs, ?_⟩
      simp [hν]
    have hMaskedI : Integrable
        (fun ω => if σ k ω = 0 then w x else F k ω) P :=
      avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
        (σ k) (hσstop k) (F k) (hFI k) (w x)
    have hMaskedUpper :=
      avram_ubv_loc6_gaussian_masked_expected_finitecap
        X hX hBV hσ hν q hq w C hC hfinite hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
        hTermMeas hCashI σ F hσstop hσle hFsource hFI k
    have hFm : ∀ᵐ ω ∂P,
        F k ω ≤ (if σ k ω = 0 then w x else F k ω) :=
      Filter.Eventually.of_forall hdom
    exact (integral_mono_ae (hFI k) hMaskedI hFm).trans hMaskedUpper
  · by_cases hσ : X.σ = 0
    · obtain ⟨Mc, Ms, Ml, G, R, hMc, hMs, hMl,
          hMc0, hMs0, hMl0, hG, hR, hbd⟩ :=
        avram_ubv_loc6_purejump_unbounded_variation_signed_budget
          X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
          hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
          n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
          hTermMeas hCashI σ F hσstop hσle hFsource hFI k
      exact hfinish Mc Ms Ml G R hMc hMs hMl
        hMc0 hMs0 hMl0 hG hR hbd
    · obtain ⟨Mc, Ms, Ml, G, R, hMc, hMs, hMl,
          hMc0, hMs0, hMl0, hG, hR, hbd⟩ :=
        avram_ubv_loc6_mixed_gaussian_negativejump_signed_budget
          X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
          hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
          n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
          hTermMeas hCashI σ F hσstop hσle hFsource hFI k
      exact hfinish Mc Ms Ml G R hMc hMs hMl
        hMc0 hMs0 hMl0 hG hR hbd
