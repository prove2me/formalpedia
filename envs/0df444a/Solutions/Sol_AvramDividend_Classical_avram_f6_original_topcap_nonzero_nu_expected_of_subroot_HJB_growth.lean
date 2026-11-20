-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_expected_of_subroot_HJB_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:57:16.375267+00:00
-- url     : https://prove2.me/submissions/61fa34e4-d70a-47dd-b8a3-e5f7db2f6f23

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_positive_psi_root_runningSup_exp_L1
import Theorems.Thm_AvramDividend_Classical_avram_gbB36_interior_cap_positive_value_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_expected_rightmesh_of_expgrowth
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω
    : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
    SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 <
    q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y <
    C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator
    w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ)
    (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D
    t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D
    t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n
    : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n :
    ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime
    𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (W Cash Term : Ω → ℝ) (hW : ∀ ω, W ω = if τ ω = 0
    ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else
    riskProcess X x D (τ ω) ω) (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
    Iic (τ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hTerm :
    ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) (hTermMeas : AEStronglyMeasurable Term
    P) (hCashI : Integrable Cash P) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ) (hσstop : ∀ k,
    IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) <
    ruinTime X x D ω then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω else riskProcess X x D (σ k
    ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ), ENNReal.ofReal (Real.exp
    (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hFI : ∀ k, Integrable (F k) P) (hCase : C = ⊤)
    (hν : X.ν ≠ 0) (θ K p lam : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hp : 0 < p) (hlam : 0 < lam) (hθlam
    : θ < lam) (hroot : X.ψ lam = p) (hwGrowth : ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y)) :
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
  letI : IsProbabilityMeasure P := X.isProbability
  have hwpos : ∀ y : ℝ, 0 ≤ y → 0 ≤ w y := by
    intro y hy
    apply avram_gbB36_interior_cap_positive_value_from_gradient
      C w hw0 hw_cont hw_smooth hw_grad y hy
    simp [hCase]
  have hExpI : Integrable
      (fun ω : Ω => Real.exp (θ * runningSup X (n : ℝ≥0) ω)) P :=
    avram_f6_original_positive_psi_root_runningSup_exp_L1
      X p lam θ hp hlam hroot hθ hθlam n
  exact avram_f6_original_topcap_expected_rightmesh_of_expgrowth
    X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
    hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
    n hn τ hτeq hτmeas hτstop W Cash Term hW hCash
    hTerm hTermMeas hCashI σ F hσstop hσle hFsource hFI
    hCase θ K hθ hK hwpos hwGrowth hExpI
