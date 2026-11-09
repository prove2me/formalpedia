-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_original_purejump_initial_condexp_stopped_source_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:23:33.155253+00:00
-- url     : https://prove2.me/submissions/df2e34cc-60fd-4dcb-aa31-5524f1948522
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_purejump_initial_eventwise_stopped_reward_budget
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
    ∀ k, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (F k) ω ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  have hm : 𝓕.rightCont 0 ≤ mΩ := (𝓕.rightCont).le 0
  have hCondStrong :
      StronglyMeasurable[𝓕.rightCont 0] (condExp (𝓕.rightCont 0) P (F k)) :=
    stronglyMeasurable_condExp
  have hCondInt : Integrable (condExp (𝓕.rightCont 0) P (F k)) P :=
    integrable_condExp
  have hCondTrim : Integrable (condExp (𝓕.rightCont 0) P (F k))
      (P.trim hm) := by
    first
    | exact hCondInt.trim hm hCondStrong
    | exact hCondInt.trim hm
  have hConstTrim : Integrable (fun _ : Ω => w x) (P.trim hm) :=
    integrable_const _
  apply ae_of_ae_trim hm
  apply ae_le_of_forall_setIntegral_le hCondTrim hConstTrim
  intro A hA hfinite
  have hTrimRestrict :
      (P.trim hm).restrict A = (P.restrict A).trim hm :=
    restrict_trim hm P hA
  have hCondSetIntegral :
      (∫ ω in A, condExp (𝓕.rightCont 0) P (F k) ω ∂(P.trim hm)) =
      (∫ ω in A, condExp (𝓕.rightCont 0) P (F k) ω ∂P) := by
    rw [hTrimRestrict]
    exact (integral_trim hm hCondStrong).symm
  have hCondIdentity :
      (∫ ω in A, condExp (𝓕.rightCont 0) P (F k) ω ∂P) =
      (∫ ω in A, F k ω ∂P) :=
    setIntegral_condExp hm (hFI k) hA
  have hCashBound :
      (∫ ω in A, F k ω ∂P) ≤ w x * (P A).toReal :=
    avram_ubv_jump11_original_purejump_initial_eventwise_stopped_reward_budget
      X hX hBV hSigmaZero q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ F hσstop hσle hFsource hFI k A hA
  calc
    (∫ ω in A, condExp (𝓕.rightCont 0) P (F k) ω ∂(P.trim hm))
        = (∫ ω in A, F k ω ∂P) := hCondSetIntegral.trans hCondIdentity
    _ ≤ w x * (P A).toReal := hCashBound
    _ = (∫ ω in A, w x ∂(P.trim hm)) := by
      simp [integral_const, Measure.real, Measure.restrict_apply,
        trim_measurableSet_eq hm hA, smul_eq_mul, mul_comm]
