-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB70_original_physical_discounted_caplinear_prepayment_postpayment_source_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:17:06.603439+00:00
-- url     : https://prove2.me/submissions/b5027a62-163e-425a-9487-eeebbdf17be8

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
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (s (i + 1)) ω - rightLimit D (s i) ω
    let V : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    e m * V (Y m) - e 0 * V (Y 0) =
      (Finset.range m).sum (fun i =>
        (e (i + 1) * V (Z i) - e i * V (Y i)) +
        e (i + 1) * (V (Y (i + 1)) - V (Z i))) := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let Y : ℕ → ℝ := fun i =>
    x + X.X (s i) ω - rightLimit D (s i) ω
  let Z : ℕ → ℝ := fun i =>
    x + X.X (s (i + 1)) ω - rightLimit D (s i) ω
  let V : ℝ → ℝ := fun y =>
    if y ≤ b then w y else w b + (y - b)
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
  change e m * V (Y m) - e 0 * V (Y 0) =
    (Finset.range m).sum (fun i =>
      (e (i + 1) * V (Z i) - e i * V (Y i)) +
      e (i + 1) * (V (Y (i + 1)) - V (Z i)))
  have hCell (i : ℕ) :
      (e (i + 1) * V (Z i) - e i * V (Y i)) +
        e (i + 1) * (V (Y (i + 1)) - V (Z i)) =
      e (i + 1) * V (Y (i + 1)) - e i * V (Y i) := by ring
  have hTel (k : ℕ) :
      (Finset.range k).sum (fun i =>
        e (i + 1) * V (Y (i + 1)) - e i * V (Y i)) =
      e k * V (Y k) - e 0 * V (Y 0) := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [Finset.sum_range_succ]
      linarith
  rw [← hTel m]
  apply Finset.sum_congr rfl
  intro i hi
  exact (hCell i).symm
