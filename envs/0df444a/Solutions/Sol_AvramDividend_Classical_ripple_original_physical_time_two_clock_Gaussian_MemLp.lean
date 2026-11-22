-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_physical_time_two_clock_Gaussian_MemLp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:40:34.497264+00:00
-- url     : https://prove2.me/submissions/8581dc2b-b118-486e-9e03-bf95f3632d61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim
import Theorems.Thm_AvramDividend_Classical_ripple_original_gaussian_gradient_between_stops_MemLp
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
/-- True original stopped Gaussian gradient in finite physical time.
The measure agrees with the original product of finite-horizon time
and path-law probability on predictable events. The random interval is genuine.
Uses Avram source physical clock and Ripple stopped-integrand L2. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ℝ≥0 × Ω → ℝ := fun p =>
         if Y p ∈ Icc u v then deriv w (Y p) else 0
       let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
       MemLp ({p : ℝ≥0 × Ω | 0 < p.1 ∧
           (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
           (p.1 : WithTop ℝ≥0) ≤ τ p.2}.indicator G) 2 μ) := by
  obtain ⟨μ, hμ, hμeq⟩ :=
    avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim X T
  refine ⟨μ, hμ, hμeq, ?_⟩
  exact ripple_original_gaussian_gradient_between_stops_MemLp
    X x D hD w a b u v hw hau huv hvb μ hμ σ τ hσstop hτstop
