-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_zerojump_finite_masked_clock_expected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:16:37.053499+00:00
-- url     : https://prove2.me/submissions/237dad0d-8ec0-4083-a240-3187032e32a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_condexp_reward_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
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
    (hFI : ∀ k, Integrable (F k) P) (hFinite : C ≠ ⊤) :
    ∀ k, (∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P) ≤ w x  := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  let A : Set Ω := {ω | σ k ω ≠ 0}
  have hA : MeasurableSet[𝓕.rightCont 0] A :=
    avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
      (σ k) (hσstop k)
  have hAm : MeasurableSet A := (𝓕.rightCont.le 0) A hA
  have hF0 :
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P (F k) ω ≤ w x :=
    avram_ubv_finite12_original_condexp_reward_budget
      X hX hBV hν q hq w C hC hFinite
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop σ F hσstop hσle hFsource hFI k
  have hC : Integrable (fun _ : Ω => w x) P :=
    integrable_const (w x)
  have hBound :
      (∫ ω in A, F k ω ∂P) ≤
      (∫ ω in A, (fun _ : Ω => w x) ω ∂P) := by
    rw [← setIntegral_condExp (𝓕.rightCont.le 0) (hFI k) hA]
    have hCondI :
        Integrable (condExp (𝓕.rightCont 0) P (F k)) P :=
      integrable_condExp
    exact setIntegral_mono_ae hCondI.integrableOn
      hC.integrableOn hF0
  have hEq :
      (fun ω : Ω => if σ k ω = 0 then w x else F k ω) =
        A.piecewise (F k) (fun _ => w x) := by
    funext ω
    by_cases hz : σ k ω = 0
    · simp [A, hz, Set.piecewise]
    · simp [A, hz, Set.piecewise]
  rw [hEq]
  calc
    (∫ ω, A.piecewise (F k) (fun _ => w x) ω ∂P)
        = (∫ ω in A, F k ω ∂P) +
          (∫ ω in Aᶜ, (fun _ : Ω => w x) ω ∂P) :=
        integral_piecewise hAm (hFI k).integrableOn hC.integrableOn
    _ ≤ (∫ ω in A, (fun _ : Ω => w x) ω ∂P) +
          (∫ ω in Aᶜ, (fun _ : Ω => w x) ω ∂P) := by
        have hs := add_le_add_right hBound
          (∫ ω in Aᶜ, (fun _ : Ω => w x) ω ∂P)
        linarith
    _ = (∫ ω, (fun _ : Ω => w x) ω ∂P) :=
        integral_add_compl hAm hC
    _ = w x := by simp
