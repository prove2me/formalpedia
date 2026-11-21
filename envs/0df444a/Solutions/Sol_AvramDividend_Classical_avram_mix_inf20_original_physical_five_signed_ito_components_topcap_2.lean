-- Prove2me | solution 2 for AvramDividend.Classical.avram_mix_inf20_original_physical_five_signed_ito_components_topcap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:13:21.213334+00:00
-- url     : https://prove2.me/submissions/2b0f788e-9289-49cf-8e09-c5ca12d17363
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_E_infinite_true_single_clock_physical_signed_reward_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_gbB36_interior_cap_positive_value_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin24_initial_event_condcentered_mask_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_positive_clock_supported_centered_of_expected
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
    SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ
    : X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont :
    ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 <
    y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y →
    ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D :
    ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) <
    ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞)
    < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X
    x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω =
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω =>
    (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ) (hσstop : ∀ k, IsStoppingTime
    𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) (hFsource : ∀ k ω, F
    k ω = Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
    x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω else riskProcess X x D (σ k ω) ω) + (∫⁻ s in
    paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
    ∂(dividendMeasure D ω)).toReal) (hFI : ∀ k, Integrable (F k) P) (hInfiniteActivity : X.ν (Iio
    (0 : ℝ)) = ⊤) (hCapCase : C = ⊤) : ∀ k, ∃ Mc Ms Ml G R : Ω → ℝ, Integrable Mc P ∧ Integrable
    Ms P ∧ Integrable Ml P ∧ (∫ ω, Mc ω ∂P) = 0 ∧ (∫ ω, Ms ω ∂P) = 0 ∧ (∫ ω, Ml ω ∂P) = 0 ∧ (∀ᵐ ω
    ∂P, σ k ω = 0 → Mc ω = 0) ∧ (∀ᵐ ω ∂P, σ k ω = 0 → Ms ω = 0) ∧ (∀ᵐ ω ∂P, σ k ω = 0 → Ml ω = 0)
    ∧ (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧ (∀ᵐ ω ∂P, F k ω ≤ w x + Mc ω + Ms ω + Ml ω + G ω +
    R ω)   := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have ht := avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable τ hτstop
  obtain ⟨W,Cash,Term,hW,hCash,hTerm,hTm,hCI⟩ :=
    avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
      X x C D hD w hw_cont hw_neg q n τ hτeq ht hτstop
  have hSrc :=
    avram_jump6_E_infinite_true_single_clock_physical_signed_reward_upper
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
      hjump n hn τ hτeq ht hτstop W Cash Term hW hCash hTerm
      hTm hCI σ F hσstop hσle hFsource hFI hCapCase hInfiniteActivity
  have hb : 0 ≤ w x :=
    avram_gbB36_interior_cap_positive_value_from_gradient
      C w hw0 hw_cont hw_smooth hw_grad x (le_of_lt hx) hxc
  intro k
  obtain ⟨M,G,R,hMI,hM0,hG,hR,hDom⟩ := hSrc k
  let A : Set Ω := {ω | σ k ω ≠ 0}
  have hAE : MeasurableSet[𝓕.rightCont 0] A :=
    avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
      (σ k) (hσstop k)
  have hA : MeasurableSet A := (𝓕.rightCont.le 0) A hAE
  have hu : ∀ᵐ ω ∂P, F k ω ≤ w x + M ω := by
    filter_upwards [hDom,hG,hR] with ω a b c; linarith
  have he : (∫ ω in A, F k ω ∂P) ≤ w x * (P A).toReal :=
    avram_mix_fin24_initial_event_condcentered_mask_transfer
      (𝓕.rightCont 0) (𝓕.rightCont.le 0) A A hAE
      (by intro ω h; exact h) (w x) hb (F k) M
      (hFI k) hMI hM0 (ae_restrict_of_ae hu)
  by_cases hp : 0 < (P A).toReal
  · obtain ⟨M',hMI',hM0',hOff,hOn⟩ :=
      avram_mix_inf20_positive_clock_supported_centered_of_expected
        A hA (F k) (hFI k) (w x) hp he
    refine ⟨M',0,0,0,0,hMI',by simp,by simp,hM0',by simp,by simp,
      ?_,?_,?_,?_,?_,?_⟩
    · exact Filter.Eventually.of_forall (fun ω hz =>
        hOff ω (by simp [A,hz]))
    · exact Filter.Eventually.of_forall (fun ω _ => rfl)
    · exact Filter.Eventually.of_forall (fun ω _ => rfl)
    · exact Filter.Eventually.of_forall (fun ω => le_refl 0)
    · exact Filter.Eventually.of_forall (fun ω => le_refl 0)
    · apply Filter.Eventually.of_forall
      intro ω
      by_cases hz : σ k ω = 0
      · have hm0 : M' ω = 0 := hOff ω (by simp [A,hz])
        have hf0 :=
          avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
            X x q w C D hD hjump (σ k) (F k) (hFsource k) ω hz
        simpa [hm0] using hf0
      · have hpos := hOn ω (by simp [A,hz])
        simpa using hpos
  · have hfinite : P A ≠ ⊤ := (measure_lt_top P A).ne
    have hPA0 : P A = 0 := by
      by_contra hnonzero
      have hpos : 0 < (P A).toReal := ENNReal.toReal_pos hnonzero hfinite
      exact (not_lt_of_ge (le_of_not_gt hp)) hpos
    have hnull : ∀ᵐ ω ∂P, ω ∉ A := by
      apply (ae_iff).2
      have hset : {a : Ω | ¬ a ∉ A} = A := by
        ext ω
        simp
      simpa only [hset] using hPA0
    refine ⟨0,0,0,0,0,by simp,by simp,by simp,by simp,by simp,by simp,
      ?_,?_,?_,?_,?_,?_⟩
    all_goals first
      | exact Filter.Eventually.of_forall (fun _ _ => rfl)
      | exact Filter.Eventually.of_forall (fun _ => le_refl 0)
      | filter_upwards [hnull] with ω hnot
        have hz : σ k ω = 0 := by
          by_contra hn
          exact hnot (by simpa [A] using hn)
        simpa using
          (avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
            X x q w C D hD hjump (σ k) (F k) (hFsource k) ω hz)
