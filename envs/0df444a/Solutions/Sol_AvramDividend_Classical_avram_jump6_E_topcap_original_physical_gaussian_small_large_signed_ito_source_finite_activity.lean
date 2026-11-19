-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_E_topcap_original_physical_gaussian_small_large_signed_ito_source_finite_activity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:58:39.064941+00:00
-- url     : https://prove2.me/submissions/e86f46bb-3f7c-4ff1-80d2-548ae19073b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

import Theorems.Thm_AvramDividend_Classical_avram_b215_original_finiteactivity_stopped_cash_initial_condexp_upper
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_condexp_upper_to_centered_majorant
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
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
    (hTop : C = ⊤) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ k, ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P (fun η => Mc η + Ms η + Ml η) ω = 0) ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        F k ω ≤ w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  have hBound : ∀ ω, σ k ω ≤ (n : ℝ≥0) := by
    intro ω
    have hb : τ ω ≤ (n : ℝ≥0) := by
      rw [hτeq ω]
      exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
    exact (hσle k ω).trans hb
  have hF0Budget : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (F k) ω ≤ w x :=
    avram_b215_original_finiteactivity_stopped_cash_initial_condexp_upper
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn (σ k) (hσstop k) hBound (F k) (hFsource k)
      (hFI k) hFinite
  obtain ⟨M, hMI, hM0, hUpper⟩ :=
    avram_mix_fin13_condexp_upper_to_centered_majorant
      (𝓕.rightCont 0) (𝓕.rightCont.le 0)
      (F k) (hFI k) (w x) hF0Budget
  refine ⟨M, (fun _ => 0), (fun _ => 0),
    (fun _ => 0), (fun _ => 0),
    hMI, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact integrable_zero Ω ℝ P
  · exact integrable_zero Ω ℝ P
  · filter_upwards [hM0] with ω hm
    simpa using hm
  · exact Filter.Eventually.of_forall (fun _ => le_refl (0 : ℝ))
  · exact Filter.Eventually.of_forall (fun _ => le_refl (0 : ℝ))
  · filter_upwards [hUpper] with ω hu
    simpa using hu
