-- Prove2me | solution 1 for AvramDividend.Classical.avram_b238_original_ruinclipped_finiteactivity_physical_stopped_source_postdividend_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:11:19.121562+00:00
-- url     : https://prove2.me/submissions/d4883cf3-7068-49df-a195-4e1deba4156e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0)
    (n m : ℕ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    let Y : ℕ → ℝ := fun i =>
      x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    e m * w (Y m) - e 0 * w (Y 0) =
      (Finset.range m).sum (fun i =>
        (e (i + 1) * w (Z i) - e i * w (Y i)) +
        e (i + 1) * (w (Y (i + 1)) - w (Z i))) := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
  let Y : ℕ → ℝ := fun i =>
    x + X.X (v i) ω - rightLimit D (v i) ω
  let Z : ℕ → ℝ := fun i =>
    x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
  change e m * w (Y m) - e 0 * w (Y 0) =
    (Finset.range m).sum (fun i =>
      (e (i + 1) * w (Z i) - e i * w (Y i)) +
      e (i + 1) * (w (Y (i + 1)) - w (Z i)))
  have hCell (i : ℕ) :
      (e (i + 1) * w (Z i) - e i * w (Y i)) +
        e (i + 1) * (w (Y (i + 1)) - w (Z i)) =
      e (i + 1) * w (Y (i + 1)) - e i * w (Y i) := by ring
  have hTel (k : ℕ) :
      (Finset.range k).sum (fun i =>
        e (i + 1) * w (Y (i + 1)) - e i * w (Y i)) =
      e k * w (Y k) - e 0 * w (Y 0) := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [Finset.sum_range_succ]
      linarith
  rw [← hTel m]
  apply Finset.sum_congr rfl
  intro i hi
  exact (hCell i).symm
