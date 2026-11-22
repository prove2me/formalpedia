-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_zerojump_postpayment_stopped_sameBrownian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T18:12:58.313299+00:00
-- url     : https://prove2.me/submissions/81a2ba61-2429-4eea-a27d-613875c09857

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_ubv_filtered_stopped_driver
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_controlled_reserve_brownian_leftCont
open MeasureTheory ProbabilityTheory Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The same original-space Brownian driver represents the whole controlled
reserve and its post-dividend stopped terminal payoff, with the original
stopping-time filtration and almost-sure left-continuous reserve paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Terminal : Ω → ℝ)
    (hTerminal : ∀ ω,
      Terminal ω =
        if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) :
    ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
      (ℱr : Filtration ℝ mΩ),
      (∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t)) ∧
      LevyStochCalc.Brownian.IsBrownianFiltration B ℱr ∧
      IsStoppingTime ℱr
        (fun ω => ((τ ω : ℝ) : WithTop ℝ)) ∧
      (∀ (t : ℝ≥0) (ω : Ω),
        riskProcess X x D t ω =
          x + (t : ℝ) * X.c + X.σ * B.W (t : ℝ) ω - D t ω) ∧
      (∀ ω,
        Terminal ω =
          if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + (τ ω : ℝ) * X.c + X.σ * B.W (τ ω : ℝ) ω -
            rightLimit D (τ ω) ω
          else x + (τ ω : ℝ) * X.c + X.σ * B.W (τ ω : ℝ) ω -
            D (τ ω) ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => riskProcess X x D u ω)
          (Set.Iic t) t) := by
  have hσ : X.σ ≠ 0 :=
    ne_of_gt (avram_p4_f4_zero_levy_ubv_sigma_pos X hBV hν)
  obtain ⟨B, ℱr, hFilEq, hBrownian, hNorm, hStop⟩ :=
    avram_lsc_zerojump_ubv_filtered_stopped_driver X hBV hν τ hτstop
  obtain ⟨_, _, hLeft⟩ :=
    avram_lsc_zerojump_original_controlled_reserve_brownian_leftCont
      X hBV hν x C D hD
  have hSource : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c + X.σ * B.W (t : ℝ) ω := by
    intro t ω
    have hNormal := hNorm (t : ℝ) ω
    simp only [Real.toNNReal_coe] at hNormal
    have hMul : B.W (t : ℝ) ω * X.σ =
        X.X t ω - (t : ℝ) * X.c :=
      (eq_div_iff hσ).mp hNormal
    nlinarith [hMul]
  refine ⟨B, ℱr, hFilEq, hBrownian, hStop, ?_, ?_, hLeft⟩
  · intro t ω
    change x + X.X t ω - D t ω =
      x + (t : ℝ) * X.c + X.σ * B.W (t : ℝ) ω - D t ω
    rw [hSource t ω]
    ring
  · intro ω
    rw [hTerminal ω]
    by_cases hCond : τ ω = 0 ∨
        (τ ω : ℝ≥0∞) < ruinTime X x D ω
    · simp only [if_pos hCond]
      rw [hSource (τ ω) ω]
      ring
    · simp only [if_neg hCond]
      change x + X.X (τ ω) ω - D (τ ω) ω =
        x + (τ ω : ℝ) * X.c + X.σ * B.W (τ ω : ℝ) ω -
          D (τ ω) ω
      rw [hSource (τ ω) ω]
      ring

