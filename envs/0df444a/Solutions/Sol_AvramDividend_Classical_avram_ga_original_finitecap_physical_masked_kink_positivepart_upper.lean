-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_physical_masked_kink_positivepart_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:13:22.07447+00:00
-- url     : https://prove2.me/submissions/d82ca4a1-af6c-4c1e-8049-9d95bcf01f0b

import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_rational_clip_gradient_ge_one
import Theorems.Thm_AvramDividend_Classical_avram_gbB54x_original_stopped_physical_grid_kink_positivepart_upper
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (δ q x : ℝ) (j : ℕ)
    (D : ℝ≥0 → Ω → ℝ) (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let α : ℝ := deriv w b
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let g : ℕ → ℝ := fun i => if a ≤ Y i then deriv w (Y i) else 1
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    let U : ℝ → ℝ := fun z => if z ≤ b then w z else w b + α * (z - b)
    max ((∑ i ∈ Finset.range (m + 1), if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) *
        (V (Y i + R i) - V (Y i) -
          (if Y i ≤ b then g i else 1) * R i)
      else 0)) 0 ≤
      max ((∑ i ∈ Finset.range (m + 1), if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) *
        (U (Y i + R i) - U (Y i) -
          (if Y i ≤ b then g i else α) * R i)
      else 0)) 0   := by
  have hα :=
    avram_ga_original_finitecap_rational_clip_gradient_ge_one
      w C hC hFiniteCap hw_grad j
  simpa only [] using
    (avram_gbB54x_original_stopped_physical_grid_kink_positivepart_upper
      X w (δ / 2)
      (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))
      (deriv w (C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))))
      q x hα D n m ρ ω)
