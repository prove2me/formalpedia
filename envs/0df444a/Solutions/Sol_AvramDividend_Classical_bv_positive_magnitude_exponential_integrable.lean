-- Prove2me | solution 1 for AvramDividend.Classical.bv_positive_magnitude_exponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:17:57.08342+00:00
-- url     : https://prove2.me/submissions/2ca2a1bd-3d47-446b-aa18-de6804e74184

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-θ * (z : ℝ)))
      (X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by
  let mag : ℝ → ℝ≥0 := fun y => Real.toNNReal (-y)
  let g : ℝ≥0 → ℝ := fun z => 1 - Real.exp (-θ * (z : ℝ))
  have hbase : IntegrableOn (fun y : ℝ => 1 - Real.exp (θ * y))
      (Iio (0 : ℝ)) X.ν := by
    have heq : (fun y : ℝ => 1 - Real.exp (θ * y)) =
        -(fun y : ℝ => Real.exp (θ * y) - 1) := by
      funext y
      simp only [Pi.neg_apply]
      ring
    rw [heq]
    exact (bv_exponential_jump_integrable X hbv θ hθ).neg
  have hind : Integrable ((Iio (0 : ℝ)).indicator
      (fun y : ℝ => 1 - Real.exp (θ * y))) X.ν :=
    hbase.integrable_indicator measurableSet_Iio
  have hpull : g ∘ mag =
      (Iio (0 : ℝ)).indicator (fun y : ℝ => 1 - Real.exp (θ * y)) := by
    funext y
    by_cases hy : y < 0
    · have hymem : y ∈ Iio (0 : ℝ) := hy
      rw [Set.indicator_of_mem hymem]
      dsimp [g, mag, Function.comp_def]
      rw [max_eq_left (by linarith)]
      congr 2
      ring
    · have hynmem : y ∉ Iio (0 : ℝ) := by simpa using hy
      rw [Set.indicator_of_notMem hynmem]
      dsimp [g, mag, Function.comp_def]
      rw [max_eq_right (by linarith)]
      simp
  have hpullInt : Integrable (g ∘ mag) X.ν := by
    rw [hpull]
    exact hind
  have hg : AEStronglyMeasurable g (X.ν.map mag) := by fun_prop
  have hmag : AEMeasurable mag X.ν := by fun_prop
  have hmap : Integrable g (X.ν.map mag) :=
    (integrable_map_measure hg hmag).2 hpullInt
  simpa [g, mag] using hmap
