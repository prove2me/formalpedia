-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger142_original_physical_gaussian_source_exact_two_error_split__v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:44:22.208657+00:00
-- url     : https://prove2.me/submissions/a96a13f7-dffa-4915-8810-1a629af3d4c7

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (ρ : Ω → ℝ≥0)
    (m : ℕ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let a : ℕ → ℝ := fun i =>
      (E (v (i + 1)) - E (v i)) * w (Y (v i))
    let b : ℕ → ℝ := fun i =>
      E (v (i + 1)) * (w (Z i) - w (Y (v i)))
    let u : ℕ → ℝ := fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        E s * (deriv w (Y s) * z +
          (iteratedDeriv 2 w (Y s) / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
    let g : ℕ → ℝ := fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0
    let h : ℕ → ℝ := fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then q * (Δ : ℝ) * E s * w (Y s) else 0
    (Finset.sum (Finset.range (m + 1)) (fun i => a i + b i)) -
      (Finset.sum (Finset.range m) u) -
      (Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          (Δ : ℝ) * E s * (X.generator w (Y s) - q * w (Y s))
        else 0)) =
      ((Finset.sum (Finset.range (m + 1)) a) +
        (Finset.sum (Finset.range m) h)) +
      ((Finset.sum (Finset.range (m + 1)) b) -
        (Finset.sum (Finset.range m) u) -
        (Finset.sum (Finset.range m) g)) := by
  dsimp only
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
  let a (i : ℕ) := (E (v (i + 1)) - E (v i)) * w (Y (v i))
  let b (i : ℕ) := E (v (i + 1)) * (w (Z i) - w (Y (v i)))
  let u (i : ℕ) :=
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    if s < ρ ω then
      let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
      E s * (deriv w (Y s) * z +
        (iteratedDeriv 2 w (Y s) / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
    else 0
  let g (i : ℕ) := let s : ℝ≥0 := (i : ℝ≥0) * Δ
    if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0
  let h (i : ℕ) := let s : ℝ≥0 := (i : ℝ≥0) * Δ
    if s < ρ ω then q * (Δ : ℝ) * E s * w (Y s) else 0
  have hcell (i : ℕ) :
      (let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          (Δ : ℝ) * E s * (X.generator w (Y s) - q * w (Y s))
        else 0) = g i - h i := by
    dsimp [g, h]; split_ifs <;> ring
  have hG :
      (Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          (Δ : ℝ) * E s * (X.generator w (Y s) - q * w (Y s))
        else 0)) = (Finset.sum (Finset.range m) (fun i => g i - h i)) :=
    Finset.sum_congr rfl (fun i hi => hcell i)
  change (Finset.sum (Finset.range (m + 1)) (fun i => a i + b i)) -
      (Finset.sum (Finset.range m) u) -
      (Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          (Δ : ℝ) * E s * (X.generator w (Y s) - q * w (Y s))
        else 0)) =
      ((Finset.sum (Finset.range (m + 1)) a) +
        (Finset.sum (Finset.range m) h)) +
      ((Finset.sum (Finset.range (m + 1)) b) -
        (Finset.sum (Finset.range m) u) -
        (Finset.sum (Finset.range m) g))
  rw [hG, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring