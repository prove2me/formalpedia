-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a110_original_gaussian_true_crossing_positive_expected_L1_from_source_and_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:46:14.189478+00:00
-- url     : https://prove2.me/submissions/657ab3f9-553a-44e9-82bf-cf9caaaf9c0c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a100_original_gaussian_true_crossing_positive_source_value_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section
/-- True original stopped Gaussian crossing positive expected error vanishes once its weighted value displacement and full physical compensator vanish in L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (n : ℕ)
    (i : ℕ → Ω → ℕ) (ρ : ℕ → Ω → ℝ≥0)
    (H : ℕ → Ω → ℝ)
    (hs : ∀ (m : ℕ) (ω : Ω), let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ < ρ m ω)
    (hc : ∀ (m : ℕ) (ω : Ω), let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ρ m ω ≤ (i m ω : ℝ≥0) * Δ + Δ) :
    let A : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      |Real.exp (-(q * (ρ m ω : ℝ)))| *
        |w ((x + X.X s ω - rightLimit D s ω) +
          (X.X (ρ m ω) ω - X.X s ω)) -
          w (x + X.X s ω - rightLimit D s ω)|
    let B : ℕ → Ω → ℝ := fun m ω => |H m ω|
    let F : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (ρ m ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      max (E (v (i m ω + 1)) *
        (w (x + X.X (v (i m ω + 1)) ω -
          rightLimit D (v (i m ω)) ω) -
          w (Y (v (i m ω)))) - H m ω) 0
    (∀ m, Integrable (A m) P) →
    (∀ m, Integrable (B m) P) →
    (∀ m, Integrable (F m) P) →
    Tendsto (fun m => ∫ ω, A m ω ∂P) atTop (𝓝 (0 : ℝ)) →
    Tendsto (fun m => ∫ ω, B m ω ∂P) atTop (𝓝 (0 : ℝ)) →
    Tendsto (fun m => ∫ ω, F m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  intro hAI hBI hFI hAt hBt
  let A : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
    |Real.exp (-(q * (ρ m ω : ℝ)))| *
      |w ((x + X.X s ω - rightLimit D s ω) +
        (X.X (ρ m ω) ω - X.X s ω)) -
        w (x + X.X s ω - rightLimit D s ω)|
  let B : ℕ → Ω → ℝ := fun m ω => |H m ω|
  let F : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (ρ m ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    max (E (v (i m ω + 1)) *
      (w (x + X.X (v (i m ω + 1)) ω -
        rightLimit D (v (i m ω)) ω) -
        w (Y (v (i m ω)))) - H m ω) 0
  change Tendsto (fun m => ∫ ω, F m ω ∂P) atTop (𝓝 (0 : ℝ))
  have hPos (m : ℕ) (ω : Ω) : 0 ≤ F m ω := by
    dsimp [F]; exact le_max_right _ 0
  have hDom (m : ℕ) (ω : Ω) : F m ω ≤ A m ω + B m ω := by
    simpa only [F, A, B] using
      (avram_ga_a100_original_gaussian_true_crossing_positive_source_value_envelope
        X x D w q (H m ω) ω n m (i m ω) (ρ m ω) (hs m ω) (hc m ω))
  have hBound (m : ℕ) :
      (∫ ω, F m ω ∂P) ≤
        (∫ ω, A m ω ∂P) + (∫ ω, B m ω ∂P) := by
    calc
      (∫ ω, F m ω ∂P) ≤ (∫ ω, A m ω + B m ω ∂P) :=
        integral_mono (hFI m) ((hAI m).add (hBI m)) (hDom m)
      _ = (∫ ω, A m ω ∂P) + (∫ ω, B m ω ∂P) :=
        integral_add (hAI m) (hBI m)
  have hTotal : Tendsto (fun m => (∫ ω, A m ω ∂P) + (∫ ω, B m ω ∂P)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using hAt.add hBt
  exact squeeze_zero (fun m => integral_nonneg (hPos m)) hBound hTotal
