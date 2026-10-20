-- Prove2me | solution 1 for AvramDividend.Classical.killedRecord_discount_scale_sandwich_of_raw_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T18:21:32.513249+00:00
-- url     : https://prove2.me/submissions/0a4e78aa-5bea-4c0f-89c0-1e58f7512c13

import Theorems.Thm_AvramDividend_Classical_killed_firstUpcrossing_weighted_sandwich
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (W : ℝ → ℝ)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h)
    (u : Ω → ℝ≥0) (G : Set Ω)
    (hu : ∀ ω ∈ G, (u ω : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : h < X.X s ω), (s : ℝ≥0∞)))
    (w : Ω → ℝ≥0∞)
    (hL : (∫⁻ ω, if ω ∈ G ∧
      (∀ t : ℝ≥0, t < u ω → h - a ≤ X.X t ω)
      then w ω else 0 ∂P) =
      ENNReal.ofReal (W (a - h) / W a))
    (hR : (∫⁻ ω, if ω ∈ G ∧
      (∀ t : ℝ≥0, t < u ω → -a ≤ X.X t ω)
      then w ω else 0 ∂P) =
      ENNReal.ofReal (W a / W (a + h))) :
    ENNReal.ofReal (W (a - h) / W a) ≤
       (∫⁻ ω, if ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω
          then w ω else 0 ∂P) ∧
       (∫⁻ ω, if ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω
          then w ω else 0 ∂P) ≤
       ENNReal.ofReal (W a / W (a + h)) := by
  obtain ⟨hLo, hHi⟩ :=
    killed_firstUpcrossing_weighted_sandwich
      X a h ha (le_of_lt hh) u G hu w
  rw [hL] at hLo
  rw [hR] at hHi
  exact ⟨hLo, hHi⟩
