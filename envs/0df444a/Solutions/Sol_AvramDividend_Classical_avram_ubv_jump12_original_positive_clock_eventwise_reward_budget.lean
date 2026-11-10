-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump12_original_positive_clock_eventwise_reward_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T12:53:58.018594+00:00
-- url     : https://prove2.me/submissions/ff4fc632-5c35-4327-8246-0c09e32568dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_initial_event_masked_stop
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward15_original_zero_normalised_stopped_reward_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q)
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
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {ω | σ k ω ≠ 0}, F k ω ∂P) ≤
        w x * (P (A ∩ {ω | σ k ω ≠ 0})).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k A hA
  let E : Set Ω := A ∩ {ω | σ k ω ≠ 0}
  have hpos : MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ k ω ≠ 0} :=
    avram_ubv_finite12_positive_clock_initial_measurable (σ k) (hσstop k)
  have hE₀ : MeasurableSet[𝓕.rightCont 0] E := hA.inter hpos
  have hE : MeasurableSet E := (𝓕.rightCont.le 0) E hE₀
  let ρ : Ω → ℝ≥0 := A.indicator (σ k)
  have hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)) :=
    avram_ubv_jump12_initial_event_masked_stop (σ k) (hσstop k) A hA
  have hρle : ∀ ω, ρ ω ≤ τ ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simpa [ρ, Set.indicator_of_mem hω] using hσle k ω
    · simp [ρ, Set.indicator_of_notMem hω]
  let G : Ω → ℝ := fun ω =>
    if ρ ω = 0 then w x else
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  have hG_eq (ω : Ω) : G ω = if ω ∈ E then F k ω else w x := by
    by_cases hω : ω ∈ A
    · by_cases hs : σ k ω = 0
      · simp [G, ρ, E, hω, hs]
      · simp [G, ρ, E, hω, hs, hFsource k ω]
    · simp [G, ρ, E, hω]
  have hI : Integrable (fun ω => if ω ∈ E then F k ω else w x) P := by
    have hI₁ : Integrable (E.indicator (F k)) P :=
      (hFI k).indicator hE
    have hI₂ : Integrable (Eᶜ.indicator (fun _ => w x)) P :=
      (integrable_const (w x)).indicator hE.compl
    have heq : (fun ω => if ω ∈ E then F k ω else w x) =
        (fun ω => E.indicator (F k) ω + Eᶜ.indicator (fun _ => w x) ω) := by
      funext ω
      by_cases hω : ω ∈ E <;> simp [Set.indicator, hω]
    rw [heq]
    exact hI₁.add hI₂
  have hGI : Integrable G P := by
    have heq : G = (fun ω => if ω ∈ E then F k ω else w x) :=
      funext hG_eq
    rw [heq]
    exact hI
  have hBudget : (∫ ω, G ω ∂P) ≤ w x :=
    avram_pj_reward15_original_zero_normalised_stopped_reward_upper
      X hX hBV hSigmaZero q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop ρ hρstop hρle hGI
  have hDisj : Disjoint E Eᶜ := by
    apply Set.disjoint_left.mpr
    intro ω hω hω'
    exact hω' hω
  have hUnion : E ∪ Eᶜ = (Set.univ : Set Ω) := by
    ext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  have hSplit (f : Ω → ℝ) (hf : Integrable f P) :
      (∫ ω, f ω ∂P) =
        (∫ ω in E, f ω ∂P) +
        (∫ ω in Eᶜ, f ω ∂P) := by
    calc
      (∫ ω, f ω ∂P) =
          (∫ ω in E ∪ Eᶜ, f ω ∂P) := by simp [hUnion]
      _ = (∫ ω in E, f ω ∂P) +
          (∫ ω in Eᶜ, f ω ∂P) :=
        setIntegral_union hDisj hE.compl hf.integrableOn hf.integrableOn
  have hGE : (∫ ω in E, G ω ∂P) = (∫ ω in E, F k ω ∂P) := by
    apply setIntegral_congr_fun hE
    intro ω hω
    simp [hG_eq ω, hω]
  have hGEc : (∫ ω in Eᶜ, G ω ∂P) = (∫ ω in Eᶜ, w x ∂P) := by
    apply setIntegral_congr_fun hE.compl
    intro ω hω
    have hnot : ω ∉ E := by simpa using hω
    simp [hG_eq ω, hnot]
  have hBudget' :
      (∫ ω in E, F k ω ∂P) +
        (∫ ω in Eᶜ, w x ∂P) ≤ w x := by
    calc
      _ = ∫ ω, G ω ∂P := by
        rw [hSplit G hGI, hGE, hGEc]
      _ ≤ w x := hBudget
  have hConst :
      (∫ ω in E, w x ∂P) +
        (∫ ω in Eᶜ, w x ∂P) = w x := by
    rw [← hSplit (fun _ => w x) (integrable_const (w x))]
    simp
  have hFinal : (∫ ω in E, F k ω ∂P) ≤ (∫ ω in E, w x ∂P) := by
    linarith
  simpa [E, integral_const, Measure.real, smul_eq_mul, mul_comm] using hFinal
