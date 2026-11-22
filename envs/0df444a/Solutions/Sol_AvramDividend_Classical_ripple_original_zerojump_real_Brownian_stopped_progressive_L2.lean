-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_zerojump_real_Brownian_stopped_progressive_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:52:33.028806+00:00
-- url     : https://prove2.me/submissions/79465dd4-c58c-4ad9-9abf-b394828d8f4f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_ubv_filtered_stopped_driver
import Theorems.Thm_AvramDividend_Classical_ripple_original_nnreal_to_real_strong_progressive
import Theorems.Thm_AvramDividend_Classical_ripple_original_two_clock_gaussian_stopped_progressive_L2
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
      (Fr : Filtration ℝ mΩ)
      (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ t : ℝ, Fr t = 𝓕.rightCont (Real.toNNReal t)) ∧
      LevyStochCalc.Brownian.IsBrownianFiltration B Fr ∧
      (∀ (t : ℝ) (ω : Ω),
        B.W t ω =
          (X.X (Real.toNNReal t) ω -
            (Real.toNNReal t : ℝ) * X.c) / X.σ) ∧
      IsStoppingTime Fr
        (fun ω => ((τ ω : ℝ) : WithTop ℝ)) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ℝ≥0 × Ω → ℝ := fun p =>
         if Y p ∈ Icc u v then deriv w (Y p) else 0
       let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
       let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
         (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
         (p.1 : WithTop ℝ≥0) ≤ τ p.2}
       LevyStochCalc.Probability.ProgressivelyMeasurable Fr
         (fun ω s => S.indicator G (Real.toNNReal s,ω)) ∧
       MemLp (S.indicator G) 2 μ) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨B, Fr, hFr, hBrown, hB, hτFr⟩ :=
    avram_lsc_zerojump_ubv_filtered_stopped_driver
      X hBV hν τ hτstop
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
    (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
    (p.1 : WithTop ℝ≥0) ≤ τ p.2}
  obtain ⟨μ, hμ, hPhysical, hProg, hLp⟩ :=
    ripple_original_two_clock_gaussian_stopped_progressive_L2
      X x D hD w a b u v hw hau huv hvb T σ τ hσstop hτstop
  have hReal : IsStronglyProgressive Fr
      (fun s ω => S.indicator G (Real.toNNReal s,ω)) :=
    ripple_original_nnreal_to_real_strong_progressive
      𝓕.rightCont Fr hFr
      (fun s ω => S.indicator G (s,ω)) hProg
  have hBrownProg : LevyStochCalc.Probability.ProgressivelyMeasurable Fr
      (fun ω s => S.indicator G (Real.toNNReal s,ω)) :=
    LevyStochCalc.Probability.ProgressivelyMeasurable.of_isStronglyProgressive hReal
  exact ⟨B, Fr, μ, hμ, hPhysical, hFr, hBrown, hB, hτFr, hBrownProg, hLp⟩
