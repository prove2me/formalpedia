-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_allUBV_finitecap_rightmesh_true_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:32:55.748217+00:00
-- url     : https://prove2.me/submissions/66913725-9480-4078-a9ef-a130378b8752

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_HJB_continuous_w_has_finitecap_K
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_all_UBV_finitecap_true_reward_dominator
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (hTermMeas : AEStronglyMeasurable Term P) (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) (hFiniteCap : C ≠ ⊤) :
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
      ∃ B : Ω → ℝ, Integrable B P ∧
        ∀ m ω, |Approx m ω| ≤ B ω := by
  intro k
  let ρ : ℕ → Ω → ℝ≥0 := fun m ω => min (τ ω) (σ k ω + 1 / ((m : ℝ≥0) + 1))
  let Approx : ℕ → Ω → ℝ := fun m ω =>
    Real.exp (-(q * (ρ m ω : ℝ))) *
      (let V : ℝ → ℝ := fun z =>
         if ENNReal.ofReal z ≤ C then w z
         else w C.toReal + (z - C.toReal)
       V (if ρ m ω = 0 ∨ (ρ m ω : ℝ≥0∞) < ruinTime X x D ω
         then x + X.X (ρ m ω) ω - rightLimit D (ρ m ω) ω
         else riskProcess X x D (ρ m ω) ω)) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ m ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  change ∃ B : Ω → ℝ, Integrable B P ∧ ∀ m ω, |Approx m ω| ≤ B ω
  obtain ⟨K, hK⟩ := avram_f6_original_HJB_continuous_w_has_finitecap_K w hw_cont C
  let Full : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  have hFullI : Integrable Full P := by
    have heq : Full = Cash := funext (fun ω => (hCash ω).symm)
    simpa only [heq] using hCashI
  have hτB : ∀ ω, τ ω ≤ (n : ℝ≥0) :=
    (avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ τ hτeq (by intro ω; exact le_rfl)).1
  have hρτ : ∀ m ω, ρ m ω ≤ τ ω := fun m ω => min_le_left _ _
  exact avram_f6_original_all_UBV_finitecap_true_reward_dominator
    X hBV x (le_of_lt hx) D hD.1.1 q (le_of_lt hq)
    w hw_neg C hFiniteCap K hK (n : ℝ≥0) τ hτB
    ρ hρτ Full (by intro ω; rfl) hFullI
    Approx (by intro m ω; rfl)
