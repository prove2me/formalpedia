-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_cell_L2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:25:36.270334+00:00
-- url     : https://prove2.me/submissions/2147165e-0cf8-4fa5-bc64-ab24ea43f7d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_multiplier_L2_cauchy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- The actual controlled discounted clipped Gaussian source coefficient preserves stopped L2 Cauchy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (s : ℝ≥0) (q K : ℝ) (hK : 0 ≤ K)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (θ η : ℕ → ℝ)
    (hθ : Filter.Tendsto θ atTop (𝓝[>] (0 : ℝ)))
    (hη : Filter.Tendsto η atTop (𝓝[>] (0 : ℝ))) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    let H : Ω → ℝ := fun ω =>
      (Real.exp (-(q * (s : ℝ))) * X.σ) *
        max (-K) (min K (G s ω))
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto (fun n : ℕ =>
      (∫ ω, (H ω * (Z (θ n) ω - Z (η n) ω)) ^ 2 ∂P))
      atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  classical
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    let y := Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
    if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
  let H : Ω → ℝ := fun ω =>
    (Real.exp (-(q * (s : ℝ))) * X.σ) *
      max (-K) (min K (G s ω))
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  change Filter.Tendsto (fun n : ℕ =>
    (∫ ω, (H ω * (Z (θ n) ω - Z (η n) ω)) ^ 2 ∂P))
      atTop (𝓝 (0 : ℝ))
  have hG : IsStronglyPredictable 𝓕.rightCont G :=
    avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
      X x D hD w C hw
  obtain ⟨hClip, hClipBound⟩ :=
    avram_wave3_04_clipped_stronglyPredictable_bounded G hG K hK
  have hHm : StronglyMeasurable H := by
    have hAt : StronglyMeasurable[𝓕.rightCont s] H :=
      (hClip.stronglyAdapted s).const_mul
        (Real.exp (-(q * (s : ℝ))) * X.σ)
    exact hAt.mono (𝓕.rightCont.le s)
  have hK0 : 0 ≤
      ‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K :=
    mul_nonneg (norm_nonneg _) hK
  have hBound : ∀ ω, |H ω| ≤
      ‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K := by
    intro ω
    change ‖(Real.exp (-(q * (s : ℝ))) * X.σ) *
      max (-K) (min K (G s ω))‖ ≤
      ‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hClipBound s ω) (norm_nonneg _)
  exact avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_multiplier_L2_cauchy
    X hν τ hτ T hbounded h H hHm
      (‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K)
      hK0 hBound θ η hθ hη
