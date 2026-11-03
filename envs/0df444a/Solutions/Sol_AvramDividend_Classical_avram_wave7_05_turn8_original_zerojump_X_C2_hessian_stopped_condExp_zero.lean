-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn8_original_zerojump_X_C2_hessian_stopped_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T01:01:24.776396+00:00
-- url     : https://prove2.me/submissions/fba0f50c-d417-49fe-a134-9e0675175f9b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_stopped_quadratic_condExp_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Direct original zerojump source stopped C2 Hessian compensated square. -/
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
    (h : ℝ≥0) (H : Ω → ℝ)
    (hHsource : H = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hHI : Integrable H P)
    (hProdI : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c) ^ 2) P) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c
    P[(fun ω =>
      H ω * (M (τ ω + h) ω - M (τ ω) ω) ^ 2 -
        ((h : ℝ) * X.σ ^ 2) * H ω) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  have hDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (X.X t ω - (t : ℝ) * X.c) +
          (0 : ℝ) + (0 : ℝ) := by
    intro t ω
    ring
  have hOne :=
    avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_stopped_quadratic_condExp_zero
      X X hν rfl (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
      hDecomp x D hD w C hw q T τ hτ B hbounded h H
      hHsource hHI hProdI
  dsimp only at hOne
  let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  change P[(fun ω =>
    H ω * (M (τ ω + h) ω - M (τ ω) ω) ^ 2 -
      ((h : ℝ) * X.σ ^ 2) * H ω) |
    (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))
  simpa only [sub_zero] using hOne
