-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_compensated_exp_centered_cross_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:33:00.924974+00:00
-- url     : https://prove2.me/submissions/4948e984-0f84-48cb-9470-44a30bea2cd2

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_one
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_exp_mixed_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Cross-moment of two centred compensated Lévy exponentials. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    ∫ ω, (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) *
      (Real.exp (η *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ η) - 1) ∂P =
        Real.exp ((h : ℝ) * (X.ψ (θ + η) - X.ψ θ - X.ψ η)) - 1 := by
  let f : Ω → ℝ := fun ω => Real.exp (θ *
    (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ)
  let g : Ω → ℝ := fun ω => Real.exp (η *
    (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ η)
  change (∫ ω, (f ω - 1) * (g ω - 1) ∂P) = _
  have hmf : (∫ ω, f ω ∂P) = 1 :=
    levy_bounded_stopping_compensated_increment_mean_one
      X τ hτ T hbounded h θ hθ
  have hmg : (∫ ω, g ω ∂P) = 1 :=
    levy_bounded_stopping_compensated_increment_mean_one
      X τ hτ T hbounded h η hη
  have hmix : (∫ ω, f ω * g ω ∂P) =
      Real.exp ((h : ℝ) * (X.ψ (θ + η) - X.ψ θ - X.ψ η)) :=
    levy_bounded_stopping_compensated_exp_mixed_moment
      X τ hτ T hbounded h θ η hθ hη
  have hf : Integrable f P := by
    apply Integrable.of_integral_ne_zero
    rw [hmf]
    norm_num
  have hg : Integrable g P := by
    apply Integrable.of_integral_ne_zero
    rw [hmg]
    norm_num
  have hfg : Integrable (fun ω => f ω * g ω) P := by
    apply Integrable.of_integral_ne_zero
    rw [hmix]
    exact Real.exp_ne_zero _
  have hfgf : Integrable (fun ω => f ω * g ω - f ω) P := hfg.sub hf
  have hfgfg : Integrable
      (fun ω => f ω * g ω - f ω - g ω) P := hfgf.sub hg
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
  have hconst : (∫ _ : Ω, (1 : ℝ) ∂P) = 1 := by simp
  calc
    (∫ ω, (f ω - 1) * (g ω - 1) ∂P) =
        ∫ ω, (f ω * g ω - f ω - g ω + 1) ∂P := by
          congr 1
          ext ω
          ring
    _ = (∫ ω, f ω * g ω ∂P) - (∫ ω, f ω ∂P) -
        (∫ ω, g ω ∂P) + (∫ _ : Ω, (1 : ℝ) ∂P) := by
          rw [integral_add hfgfg hone]
          rw [integral_sub hfgf hg]
          rw [integral_sub hfg hf]
    _ = Real.exp ((h : ℝ) * (X.ψ (θ + η) - X.ψ θ - X.ψ η)) - 1 := by
          rw [hmix, hmf, hmg, hconst]
          ring
