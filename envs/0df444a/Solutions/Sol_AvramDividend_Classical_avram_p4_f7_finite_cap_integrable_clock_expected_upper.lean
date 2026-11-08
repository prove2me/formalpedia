-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f7_finite_cap_integrable_clock_expected_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:00:25.639008+00:00
-- url     : https://prove2.me/submissions/78e98f3f-5c57-4912-85c1-5b70ca3bffd4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_zero_nu_finitecap_positive_clock_gaussian_ito
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_purejump_unbounded_variation_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_mixed_gaussian_negativejump_signed_budget

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
    (hFI : ∀ k, Integrable (F k) P) (hfinite : C ≠ ⊤) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hzero (k : ℕ) (ω : Ω) (hz : σ k ω = 0) : F k ω ≤ w x := by
    exact avram_ubv_loc6_original_zero_clock_exact_physical_F_le
      X x q w C D hD hjump σ F hFsource k ω hz
  have hcombine (k : ℕ) (Mc Ms Ml G R : Ω → ℝ)
      (hMc : Integrable Mc P) (hMs : Integrable Ms P)
      (hMl : Integrable Ml P)
      (hMc0 : (∫ ω, Mc ω ∂P) = 0)
      (hMs0 : (∫ ω, Ms ω ∂P) = 0)
      (hMl0 : (∫ ω, Ml ω ∂P) = 0)
      (hG : ∀ᵐ ω ∂P, G ω ≤ 0) (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
      (hbd : ∀ᵐ ω ∂P,
        (if σ k ω = 0 then w x else F k ω) ≤
          w x + Mc ω + Ms ω + Ml ω + G ω + R ω) :
      ∃ M : Ω → ℝ, Integrable M P ∧
        (∫ ω, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, F k ω ≤ w x + M ω) := by
    refine ⟨fun ω => Mc ω + Ms ω + Ml ω, (hMc.add hMs).add hMl, ?_, ?_⟩
    · calc
        (∫ ω, Mc ω + Ms ω + Ml ω ∂P) =
            (∫ ω, Mc ω + Ms ω ∂P) + (∫ ω, Ml ω ∂P) := by
              simpa only [Pi.add_apply] using (integral_add (hMc.add hMs) hMl)
        _ = (∫ ω, Mc ω ∂P) + (∫ ω, Ms ω ∂P) +
            (∫ ω, Ml ω ∂P) := by simpa only [Pi.add_apply] using (congrArg (fun z : ℝ => z + (∫ ω, Ml ω ∂P)) (integral_add hMc hMs))
        _ = 0 := by rw [hMc0, hMs0, hMl0]; ring
    · filter_upwards [hG, hR, hbd] with ω hGω hRω hbdω
      have haux : F k ω ≤ (if σ k ω = 0 then w x else F k ω) := by
        split_ifs with hz0
        · exact hzero k ω hz0
        · exact le_rfl
      linarith
  have hbudget : ∀ k, ∃ M : Ω → ℝ,
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, F k ω ≤ w x + M ω) := by
    intro k
    by_cases hν : X.ν = 0
    · obtain ⟨Mc, G, R, hMc, hMc0, hMzero, hG, hR, hbd⟩ :=
        avram_ubv_loc6_zero_nu_finitecap_positive_clock_gaussian_ito
          X hX hBV hν q hq w C hC hfinite hw0 hw_cont hw_neg
          hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
          τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
          hTermMeas hCashI σ F hσstop hσle hFsource hFI k
      refine ⟨Mc, hMc, hMc0, ?_⟩
      filter_upwards [hG, hR, hbd] with ω hGω hRω hbdω
      by_cases hz0 : σ k ω = 0
      · simpa [hMzero ω hz0] using hzero k ω hz0
      · have hbound := hbdω hz0
        linarith
    · by_cases hσ : X.σ = 0
      · obtain ⟨Mc, Ms, Ml, G, R, hMc, hMs, hMl,
            hMc0, hMs0, hMl0, hG, hR, hbd⟩ :=
          avram_ubv_loc6_purejump_unbounded_variation_signed_budget
            X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
            hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
            τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
            hTermMeas hCashI σ F hσstop hσle hFsource hFI k
        exact hcombine k Mc Ms Ml G R hMc hMs hMl hMc0 hMs0 hMl0 hG hR hbd
      · obtain ⟨Mc, Ms, Ml, G, R, hMc, hMs, hMl,
            hMc0, hMs0, hMl0, hG, hR, hbd⟩ :=
          avram_ubv_loc6_mixed_gaussian_negativejump_signed_budget
            X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
            hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
            τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
            hTermMeas hCashI σ F hσstop hσle hFsource hFI k
        exact hcombine k Mc Ms Ml G R hMc hMs hMl hMc0 hMs0 hMl0 hG hR hbd
  intro k
  obtain ⟨M, hMi, hM0, hFM⟩ := hbudget k
  have hConst : Integrable (fun _ : Ω => w x) P := integrable_const (w x)
  have hUpper : (∫ ω, F k ω ∂P) ≤ (∫ ω, w x + M ω ∂P) :=
    integral_mono_ae (hFI k) (hConst.add hMi) hFM
  have hEval : (∫ ω, w x + M ω ∂P) = w x := by
    rw [integral_add hConst hMi]
    simp [hM0]
  calc
    (∫ ω, F k ω ∂P) ≤ (∫ ω, w x + M ω ∂P) := hUpper
    _ = w x := hEval
