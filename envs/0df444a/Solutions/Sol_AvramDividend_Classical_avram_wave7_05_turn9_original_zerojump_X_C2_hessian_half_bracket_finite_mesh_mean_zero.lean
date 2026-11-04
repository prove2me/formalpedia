-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn9_original_zerojump_X_C2_hessian_half_bracket_finite_mesh_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:16:47.386687+00:00
-- url     : https://prove2.me/submissions/14421722-6dec-4103-8906-1d8e99c66af3

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_finite_half_bracket_mean_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Direct original zerojump X C2 stopped Hessian half-bracket finite mesh compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0)
    (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (H : ι → Ω → ℝ)
    (hHsource : ∀ i ∈ S, H i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (BH : ι → ℝ)
    (hBH : ∀ i ∈ S, 0 ≤ BH i)
    (hHbound : ∀ i ∈ S, ∀ ω, |H i ω| ≤ BH i) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c
    let V : ι → Ω → ℝ := fun i ω =>
      M (τ i ω + h i) ω - M (τ i ω) ω
    let Q : ι → Ω → ℝ := fun i ω =>
      (1 / 2 : ℝ) * (((1 : ℝ) * V i ω) * (H i ω * V i ω)) -
        (((h i : ℝ) * X.σ ^ 2) / 2) * H i ω
    Integrable (fun ω => ∑ i ∈ S, Q i ω) P ∧
    (∫ ω, ∑ i ∈ S, Q i ω ∂P) = 0 := by
  classical
  have hSource : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (X.X t ω - (t : ℝ) * X.c) + (0 : ℝ) + (0 : ℝ) := by
    intro t ω
    ring
  have hOne :=
    avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_finite_half_bracket_mean_zero
      X X hν rfl (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
      hSource x D hD w C hw q T S τ hτ B hbounded
      h H hHsource BH hBH hHbound
  dsimp only at hOne
  simpa only [sub_zero] using hOne
