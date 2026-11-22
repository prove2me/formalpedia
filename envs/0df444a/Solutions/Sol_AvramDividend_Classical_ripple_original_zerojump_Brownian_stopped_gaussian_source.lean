-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_zerojump_Brownian_stopped_gaussian_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:03:58.601294+00:00
-- url     : https://prove2.me/submissions/e9dc93f4-34b2-4ffa-8f34-e91aa3eccff2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_postpayment_stopped_sameBrownian
import Theorems.Thm_AvramDividend_Classical_ripple_original_physical_time_two_clock_Gaussian_MemLp
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
      (ℱr : Filtration ℝ mΩ)
      (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t)) ∧
      LevyStochCalc.Brownian.IsBrownianFiltration B ℱr ∧
      IsStoppingTime ℱr
        (fun ω => ((τ ω : ℝ) : WithTop ℝ)) ∧
      (∀ (t : ℝ≥0) (ω : Ω),
        riskProcess X x D t ω =
          x + (t : ℝ) * X.c + X.σ * B.W (t : ℝ) ω - D t ω) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
         (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ℝ≥0 × Ω → ℝ := fun p =>
         if Y p ∈ Icc u v then deriv w (Y p) else 0
       let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
       MemLp ({p : ℝ≥0 × Ω | 0 < p.1 ∧
         (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
         (p.1 : WithTop ℝ≥0) ≤ τ p.2}.indicator G) 2 μ)  := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Terminal : Ω → ℝ := fun ω => if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω
  have hTerminal : ∀ ω,
      Terminal ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω := by
    intro ω
    rfl
  obtain ⟨B, ℱr, hF, hBrown, hStop, hRisk, _, _⟩ :=
    avram_lsc_zerojump_postpayment_stopped_sameBrownian
      X hBV hν x C D hD τ hτstop Terminal hTerminal
  obtain ⟨μ, hμ, hPhysical, hLp⟩ :=
    ripple_original_physical_time_two_clock_Gaussian_MemLp
      X x D hD.1.1 w a b u v hw hau huv hvb T σ τ hσstop hτstop
  exact ⟨B, ℱr, μ, hμ, hPhysical, hF, hBrown, hStop, hRisk, hLp⟩
