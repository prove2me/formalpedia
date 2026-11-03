-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn6_original_zerojump_stopped_C2_gaussian_bounded_ito_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:13:12.26022+00:00
-- url     : https://prove2.me/submissions/fb1f2d06-0300-4e16-8383-8b8faf5ccf85

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_controlled_C2_gaussian_one_cell_centered_martingale
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! On the actual original X with zero jump measure, bounded source C2
gradient and Hessian yield a completely integrable centred half-bracket
Gaussian one-cell Ito residual without separate moment hypotheses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0)
    (KG KH : ℝ) (hKG : 0 ≤ KG) (hKH : 0 ≤ KH) :
    let G : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let H : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    (∀ ω, |G ω| ≤ KG) →
    (∀ ω, |H ω| ≤ KH) →
    let V : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => G ω * V ω +
      (1 / 2 : ℝ) * (H ω * ((V ω) ^ 2 - (h : ℝ) * X.σ ^ 2))) P ∧
    (∫ ω, G ω * V ω +
      (1 / 2 : ℝ) * (H ω * ((V ω) ^ 2 - (h : ℝ) * X.σ ^ 2)) ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let G : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
  let H : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
  let V : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  dsimp only
  intro hGB hHB
  have hPred :=
    avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
      X x D hD w C hw q T τ hτ
  dsimp only at hPred
  have hHI : Integrable H P := by
    apply Integrable.of_bound hPred.2.2.2.aestronglyMeasurable KH
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hHB ω)
  have hOneBound : ∀ ω : Ω, |(1 : ℝ)| ≤ 1 := by
    intro ω
    norm_num
  have hCov :=
    avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
      X hν τ hτ B hbounded h (fun _ => (1 : ℝ)) H
        measurable_const hPred.2.1 measurable_const hPred.2.2.2
        1 KH (by norm_num) hKH hOneBound hHB
  dsimp only at hCov
  have hWeighted : Integrable (fun ω => H ω * (V ω) ^ 2) P := by
    have hEq : (fun ω => H ω * (V ω) ^ 2) =
        (fun ω => ((1 : ℝ) * V ω) * (H ω * V ω)) := by
      funext ω
      ring
    rw [hEq]
    exact hCov.1
  have hOne :=
    avram_wave7_05_turn3_original_controlled_C2_gaussian_one_cell_centered_martingale
      X hν x D hD w C hw q T τ hτ B hbounded h
        KG hKG hGB hHI hWeighted
  dsimp only at hOne
  exact hOne
