-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn8_original_zerojump_X_C2_taylor_stopped_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:57:30.926703+00:00
-- url     : https://prove2.me/submissions/9228d29f-1dc4-48d9-a6aa-19a19c85794d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn8_original_allnu_Xminusjump_C2_taylor_stopped_condExp_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Original zerojump X C2 stopped Taylor residual conditional expectation zero. -/
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
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGsource : G = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hHsource : H = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hGI : Integrable (fun ω => G ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) P)
    (hHI : Integrable H P)
    (hH2I : Integrable (fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c
    let V : Ω → ℝ := fun ω => M (τ ω + h) ω - M (τ ω) ω
    let R : Ω → ℝ := fun ω =>
      G ω * V ω + (1 / 2 : ℝ) * H ω *
        (V ω ^ 2 - (h : ℝ) * X.σ ^ 2)
    Integrable R P ∧
      P[R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  have hDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (X.X t ω - (t : ℝ) * X.c) +
          (0 : ℝ) + (0 : ℝ) := by
    intro t ω
    ring
  have hOne :=
    avram_wave7_05_turn8_original_allnu_Xminusjump_C2_taylor_stopped_condExp_zero
      X X hν rfl (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
      hDecomp x D hD w C hw q T τ hτ B hbounded h G H
      hGsource hHsource hGI hHI hH2I
  dsimp only at hOne
  let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  let V : Ω → ℝ := fun ω => M (τ ω + h) ω - M (τ ω) ω
  let R : Ω → ℝ := fun ω =>
    G ω * V ω + (1 / 2 : ℝ) * H ω *
      (V ω ^ 2 - (h : ℝ) * X.σ ^ 2)
  change Integrable R P ∧
    P[R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))
  simpa only [sub_zero] using hOne
