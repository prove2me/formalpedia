-- Prove2me | solution 3 for AvramDividend.Classical.avram_mix_fin28_original_one_clock_positive_event_cash_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:35:14.811237+00:00
-- url     : https://prove2.me/submissions/13ab74bd-6826-488e-aee5-da5ab94689da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_b235_original_finiteactivity_ruinclipped_stopped_cash_initial_condexp_upper
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-!
The finite-cap reward is integrable; conditional expectation controls each
initial positive-clock event by its defining set-integral property.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (G : Ω → ℝ)
    (hGsource : ∀ ω, G ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨
              (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤) :
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {ω : Ω | ρ ω ≠ 0}, G ω ∂P) ≤
        w x * (P (A ∩ {ω : Ω | ρ ω ≠ 0})).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hGI : Integrable G P :=
    avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
      X x q (le_of_lt hq) w hw_cont hw_neg
      C hCfinite hxc D hD n ρ hρstop hρbound G hGsource
  have hCond :
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P G ω ≤ w x :=
    avram_b235_original_finiteactivity_ruinclipped_stopped_cash_initial_condexp_upper
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn ρ hρstop hρbound hρclip G hGsource hGI hFiniteActivity
  have hPositive :
      MeasurableSet[𝓕.rightCont 0] {ω : Ω | ρ ω ≠ 0} :=
    avram_ubv_finite12_positive_clock_initial_measurable ρ hρstop
  intro A hA
  let E : Set Ω := A ∩ {ω : Ω | ρ ω ≠ 0}
  have hE : MeasurableSet[𝓕.rightCont 0] E := hA.inter hPositive
  have hSetCond :
      (∫ ω in E, condExp (𝓕.rightCont 0) P G ω ∂P) =
        ∫ ω in E, G ω ∂P :=
    setIntegral_condExp ((𝓕.rightCont).le 0) hGI hE
  have hMono :
      (∫ ω in E, condExp (𝓕.rightCont 0) P G ω ∂P) ≤
        ∫ ω in E, (w x : ℝ) ∂P := by
    exact integral_mono_ae
      (integrable_condExp.integrableOn)
      (integrable_const (w x))
      (ae_restrict_of_ae hCond)
  calc
    (∫ ω in E, G ω ∂P) =
        ∫ ω in E, condExp (𝓕.rightCont 0) P G ω ∂P :=
      hSetCond.symm
    _ ≤ ∫ ω in E, (w x : ℝ) ∂P := hMono
    _ = w x * (P E).toReal := by
      simp [setIntegral_const, smul_eq_mul, mul_comm]
      left
      rfl
