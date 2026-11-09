-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail12_original_discounted_uniform_generator_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:30:19.561119+00:00
-- url     : https://prove2.me/submissions/d8451aeb-2550-40e6-abef-798635aa7e3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_original_generator_uniform_near_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An actual discounted uniform-grid generator cell is arbitrarily negative
when the pre-dividend reserve enters the singular near-zero neighbourhood. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0) (K n : ℕ) (T t y : ℝ)
    (hy : 0 < y) (hy1 : y < 1)
    (hy_small : y ≤ (1 / ((K : ℝ) + 4)) ^ 4)
    (hweight : 1 / ((K : ℝ) + 4) ≤
      Real.exp (-t) * (T / ((n : ℝ) + 2))) :
    Real.exp (-t) *
      (X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) y -
        (1 + y)) * (T / ((n : ℝ) + 2)) ≤ -(K : ℝ) := by
  let g : ℝ := X.generator
    (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) y - (1 + y)
  let a : ℝ := 1 / ((K : ℝ) + 4)
  let b : ℝ := Real.exp (-t) * (T / ((n : ℝ) + 2))
  have hcore : a * g ≤ -(K : ℝ) := by
    simpa only [a, g] using
      avram_bv_tail12_original_generator_uniform_near_zero
        X hBV hν hc K y hy hy1 hy_small
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hk : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
  have hg : g ≤ 0 := by
    by_contra h
    have hpos : 0 < g := lt_of_not_ge h
    have hmul : 0 < a * g := mul_pos ha hpos
    linarith
  have hcomp : b * g ≤ a * g :=
    mul_le_mul_of_nonpos_right (show a ≤ b from hweight) hg
  calc
    Real.exp (-t) *
        (X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) y -
          (1 + y)) * (T / ((n : ℝ) + 2)) = b * g := by
      dsimp [b, g]
      ring
    _ ≤ a * g := hcomp
    _ ≤ -(K : ℝ) := hcore
