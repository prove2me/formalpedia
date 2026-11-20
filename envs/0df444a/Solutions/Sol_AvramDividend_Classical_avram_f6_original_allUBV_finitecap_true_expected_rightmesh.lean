-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_allUBV_finitecap_true_expected_rightmesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:33:17.500686+00:00
-- url     : https://prove2.me/submissions/45e48d0a-e7df-47c0-89d7-3a72f1ce4e43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_rightmesh_expected_limit_of_domination
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_allUBV_finitecap_rightmesh_true_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_physical_rightmesh_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_any_clock_caplinear_reward_regular
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_actual_discounted_caplinear_terminal_rightmesh_limit
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_actual_discounted_cash_rightmesh_tends_to_subclock
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
    SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 <
    q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y <
    C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator
    w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ)
    (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t
    ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω
    ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ)
    (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω
    : WithTop ℝ≥0))) (W Cash Term : Ω → ℝ) (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X
    x D ω then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω) (hCash : ∀
    ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ), ENNReal.ofReal (Real.exp
    (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ)))
    * w (W ω)) (hTermMeas : AEStronglyMeasurable Term P) (hCashI : Integrable Cash P) (σ : ℕ → Ω →
    ℝ≥0) (F : ℕ → Ω → ℝ) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop
    ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) *
    w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ k ω) ω - rightLimit D (σ k
    ω) ω else riskProcess X x D (σ k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω
    : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hFI : ∀ k,
    Integrable (F k) P) (hFiniteCap : C ≠ ⊤) :
    ∀ k,
      let ρ : ℕ → Ω → ℝ≥0 := fun m ω =>
        min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1)))
      let Approx : ℕ → Ω → ℝ := fun m ω =>
        Real.exp (-(q * (ρ m ω : ℝ))) *
          (let V : ℝ → ℝ := fun z =>
             if ENNReal.ofReal z ≤ C then w z
             else w C.toReal + (z - C.toReal)
           V (if ρ m ω = 0 ∨
               (ρ m ω : ℝ≥0∞) < ruinTime X x D ω then
                x + X.X (ρ m ω) ω - rightLimit D (ρ m ω) ω
              else riskProcess X x D (ρ m ω) ω)) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ m ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      Tendsto (fun m : ℕ => ∫ ω, Approx m ω ∂P) atTop
        (nhds ((∫ ω,
        Real.exp (-(q * (σ k ω : ℝ))) *
          (let V : ℝ → ℝ := fun z =>
             if ENNReal.ofReal z ≤ C then w z
             else w C.toReal + (z - C.toReal)
           V (if σ k ω = 0 ∨
               (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
               x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
             else riskProcess X x D (σ k ω) ω)) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal ∂P)))  := by
  intro k
  let ρ : ℕ → Ω → ℝ≥0 := fun m ω =>
    min (τ ω) (σ k ω + 1 / ((m : ℝ≥0) + 1))
  let V : ℝ → ℝ := fun z =>
    if ENNReal.ofReal z ≤ C then w z else w C.toReal + (z - C.toReal)
  let R : (Ω → ℝ≥0) → Ω → ℝ := fun t ω =>
    Real.exp (-(q * (t ω : ℝ))) *
      V (if t ω = 0 ∨ (t ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (t ω) ω - rightLimit D (t ω) ω
        else riskProcess X x D (t ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  change Tendsto (fun m => ∫ ω, R (ρ m) ω ∂P) atTop
    (𝓝 (∫ ω, R (σ k) ω ∂P))
  obtain ⟨B, hBI, hBound⟩ :=
    avram_f6_original_allUBV_finitecap_rightmesh_true_L1_envelope
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash
      hTerm hTermMeas hCashI σ F hσstop hσle hFsource hFI
      hFiniteCap k
  apply avram_f6_original_true_rightmesh_expected_limit_of_domination
    X x D q w C (σ k) τ ρ V R B hBI
  · intro m
    have hs := avram_f6_original_physical_rightmesh_isStoppingTime
      τ (σ k) hτstop (hσstop k)
      (1 / ((m : ℝ≥0) + 1))
    have hreg := avram_f6_original_any_clock_caplinear_reward_regular
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q (ρ m) (by simpa [ρ] using hs)
    exact hreg.1.aestronglyMeasurable
  · intro m
    exact Filter.Eventually.of_forall (fun ω => by
      change |R (ρ m) ω| ≤ B ω
      exact hBound m ω)
  · apply Filter.Eventually.of_forall
    intro ω
    have hr := (avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ τ hτeq (fun _ => le_rfl)).2 ω
    have ht := avram_f6_original_actual_discounted_caplinear_terminal_rightmesh_limit
      X x C w hw_cont D hD q ω (σ k ω) (τ ω) (hσle k ω) hr
    have hc := avram_f6_original_actual_discounted_cash_rightmesh_tends_to_subclock
      X x D hD.1.1 q (le_of_lt hq) ω (σ k ω) (τ ω) (hσle k ω)
    simpa only [R, ρ, V] using ht.add hc
