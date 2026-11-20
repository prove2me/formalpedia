-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_rightmesh_all_real_rewards_measurable_and_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:15:29.923095+00:00
-- url     : https://prove2.me/submissions/4f0b902c-f4ea-4f74-8c92-20fa8286a183

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_stopped_reward_real_caplinear_cash_exact
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_NNReal_positive_shift_stopping
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_any_clock_caplinear_reward_regular
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X
    : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0
    < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y
    < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧
    X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv
    w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD :
    IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
    0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D
    ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω -
    (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min
    (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop
    : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (W Cash Term : Ω → ℝ) (hW : ∀
    ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (τ ω) ω - rightLimit D (τ
    ω) ω else riskProcess X x D (τ ω) ω) (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime
    X x D ω) ∩ Iic (τ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D
    ω)).toReal) (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) (hTermMeas :
    AEStronglyMeasurable Term P) (hCashI : Integrable Cash P) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ
    k ω ≤ τ ω) (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨ (σ k
    ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω else
    riskProcess X x D (σ k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
    ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hFI : ∀ k, Integrable
    (F k) P) :
    ∀ k,
      let V : ℝ → ℝ := fun z =>
        if ENNReal.ofReal z ≤ C then w z
        else w C.toReal + (z - C.toReal)
      let ρ : ℕ → Ω → ℝ≥0 := fun m ω =>
        min (τ ω) (σ k ω + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
      let Approx : ℕ → Ω → ℝ := fun m ω =>
        Real.exp (-(q * (ρ m ω : ℝ))) *
          V (if ρ m ω = 0 ∨ (ρ m ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ m ω) ω - rightLimit D (ρ m ω) ω
            else riskProcess X x D (ρ m ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ m ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let Z : Ω → ℝ := fun ω =>
        Real.exp (-(q * (σ k ω : ℝ))) *
          V (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
            else riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      AEStronglyMeasurable Z P ∧ (0 ≤ᵐ[P] Z) ∧
        (∀ m, Measurable (Approx m)) ∧
        (∀ m, 0 ≤ᵐ[P] Approx m) := by
  intro k
  let ρ : ℕ → Ω → ℝ≥0 := fun m ω =>
    min (τ ω) (σ k ω + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
  let V : ℝ → ℝ := fun z =>
    if ENNReal.ofReal z ≤ C then w z else w C.toReal + (z - C.toReal)
  let R : (Ω → ℝ≥0) → Ω → ℝ := fun c ω =>
    Real.exp (-(q * (c ω : ℝ))) *
      V (if c ω = 0 ∨ (c ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (c ω) ω - rightLimit D (c ω) ω
        else riskProcess X x D (c ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (c ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  change AEStronglyMeasurable (R (σ k)) P ∧
    (0 ≤ᵐ[P] R (σ k)) ∧
    (∀ m, Measurable (R (ρ m))) ∧ (∀ m, 0 ≤ᵐ[P] R (ρ m))
  have hV (z : ℝ) : V z =
      (if C = ⊤ then w z else if z ≤ C.toReal then w z
       else w C.toReal + (z - C.toReal)) := by
    by_cases ht : C = ⊤
    · simp [V, ht]
    · simp [V, ht, ENNReal.ofReal_le_iff_le_toReal ht]
  have hZEQ : R (σ k) = F k := by
    funext ω
    have hs := avram_f6_original_stopped_reward_real_caplinear_cash_exact
      X x C hC hxc w D hD q σ F hFsource k ω
    dsimp only at hs
    simpa only [R, V, hV] using hs.symm
  have hreg (c : Ω → ℝ≥0)
      (hc : IsStoppingTime 𝓕.rightCont
        (fun ω => (c ω : WithTop ℝ≥0))) :
      Measurable (R c) ∧ (∀ ω, 0 ≤ R c ω) := by
    simpa only [R, V] using
      (avram_f6_original_any_clock_caplinear_reward_regular
        X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hxc D hD q c hc)
  have hρstop (m : ℕ) : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ m ω : WithTop ℝ≥0)) := by
    have hshift := avram_f6_original_NNReal_positive_shift_stopping
      (σ k) (hσstop k) ((1 : ℝ≥0) / ((m : ℝ≥0) + 1))
    simpa [ρ] using hτstop.min hshift
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hZEQ]; exact (hFI k).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (hreg (σ k) (hσstop k)).2
  · intro m; exact (hreg (ρ m) (hρstop m)).1
  · intro m; exact Filter.Eventually.of_forall (hreg (ρ m) (hρstop m)).2
