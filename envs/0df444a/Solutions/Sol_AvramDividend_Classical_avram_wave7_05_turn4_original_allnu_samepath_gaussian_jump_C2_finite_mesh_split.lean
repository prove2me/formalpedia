-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_finite_mesh_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:57:28.208139+00:00
-- url     : https://prove2.me/submissions/7d5cbbec-7625-4c07-9044-416825d80f13

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_cell_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (M Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c + M t ω + Jsmall t ω + Jlarge t ω)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (h : ι → ℝ≥0) :
    let G : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let H : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let A : ι → Ω → ℝ := fun i ω =>
      X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
    let B : ι → Ω → ℝ := fun i ω =>
      M (τ i ω + h i) ω - M (τ i ω) ω
    let J : ι → Ω → ℝ := fun i ω =>
      (Jsmall (τ i ω + h i) ω - Jsmall (τ i ω) ω) +
      (Jlarge (τ i ω + h i) ω - Jlarge (τ i ω) ω)
    ∀ ω,
      Finset.sum S (fun i => G i ω * A i ω +
        (1 / 2 : ℝ) * H i ω * (A i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) =
      Finset.sum S (fun i => G i ω * B i ω +
        (1 / 2 : ℝ) * H i ω * (B i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) +
      Finset.sum S (fun i => G i ω * J i ω + H i ω * B i ω * J i ω +
        (1 / 2 : ℝ) * H i ω * J i ω ^ 2) := by
  classical
  let G : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
  let H : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
  let A : ι → Ω → ℝ := fun i ω =>
    X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
  let B : ι → Ω → ℝ := fun i ω =>
    M (τ i ω + h i) ω - M (τ i ω) ω
  let J : ι → Ω → ℝ := fun i ω =>
    (Jsmall (τ i ω + h i) ω - Jsmall (τ i ω) ω) +
    (Jlarge (τ i ω + h i) ω - Jlarge (τ i ω) ω)
  change ∀ ω,
      Finset.sum S (fun i => G i ω * A i ω +
        (1 / 2 : ℝ) * H i ω * (A i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) =
      Finset.sum S (fun i => G i ω * B i ω +
        (1 / 2 : ℝ) * H i ω * (B i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) +
      Finset.sum S (fun i => G i ω * J i ω + H i ω * B i ω * J i ω +
        (1 / 2 : ℝ) * H i ω * J i ω ^ 2)
  intro ω
  calc
    Finset.sum S (fun i => G i ω * A i ω +
        (1 / 2 : ℝ) * H i ω * (A i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) =
      ∑ i ∈ S, ((G i ω * B i ω +
        (1 / 2 : ℝ) * H i ω * (B i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) +
        (G i ω * J i ω + H i ω * B i ω * J i ω +
          (1 / 2 : ℝ) * H i ω * J i ω ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hCell :=
              avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_cell_split
                X x D hD w C hw q T M Jsmall Jlarge hSourceDecomp
                (τ i) (hτ i hi) (h i)
            dsimp only at hCell
            exact hCell ω
    _ = Finset.sum S (fun i => G i ω * B i ω +
        (1 / 2 : ℝ) * H i ω * (B i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) +
      Finset.sum S (fun i => G i ω * J i ω + H i ω * B i ω * J i ω +
        (1 / 2 : ℝ) * H i ω * J i ω ^ 2) := by
          rw [Finset.sum_add_distrib]
