-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_cell_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:51:28.208707+00:00
-- url     : https://prove2.me/submissions/785a3ae5-ab59-442b-bb65-4ada1ba21005

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (M Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c + M t ω + Jsmall t ω + Jlarge t ω)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (h : ℝ≥0) :
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
    let A : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let B : Ω → ℝ := fun ω =>
      M (τ ω + h) ω - M (τ ω) ω
    let J : Ω → ℝ := fun ω =>
      (Jsmall (τ ω + h) ω - Jsmall (τ ω) ω) +
      (Jlarge (τ ω + h) ω - Jlarge (τ ω) ω)
    ∀ ω,
      G ω * A ω + (1 / 2 : ℝ) * H ω * (A ω ^ 2 - (h : ℝ) * X.σ ^ 2) =
      (G ω * B ω + (1 / 2 : ℝ) * H ω *
        (B ω ^ 2 - (h : ℝ) * X.σ ^ 2)) +
      (G ω * J ω + H ω * B ω * J ω + (1 / 2 : ℝ) * H ω * J ω ^ 2) := by
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
  let A : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let B : Ω → ℝ := fun ω =>
    M (τ ω + h) ω - M (τ ω) ω
  let J : Ω → ℝ := fun ω =>
    (Jsmall (τ ω + h) ω - Jsmall (τ ω) ω) +
    (Jlarge (τ ω + h) ω - Jlarge (τ ω) ω)
  change ∀ ω, G ω * A ω + (1 / 2 : ℝ) * H ω *
      (A ω ^ 2 - (h : ℝ) * X.σ ^ 2) =
    (G ω * B ω + (1 / 2 : ℝ) * H ω *
      (B ω ^ 2 - (h : ℝ) * X.σ ^ 2)) +
    (G ω * J ω + H ω * B ω * J ω + (1 / 2 : ℝ) * H ω * J ω ^ 2)
  intro ω
  have hInc : A ω = B ω + J ω := by
    dsimp [A, B, J]
    rw [hSourceDecomp (τ ω + h) ω, hSourceDecomp (τ ω) ω]
    push_cast
    ring
  rw [hInc]
  ring
