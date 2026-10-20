-- Prove2me | solution 1 for AvramDividend.Classical.chat03_capped_grid_scale_value_negative_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:57:03.035827+00:00
-- url     : https://prove2.me/submissions/1477c86b-d087-4565-999e-7077ce79a846

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_stopped_path_open_eventually
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
At a strictly negative limiting stopped reserve the scale function is
identically zero in a right neighbourhood of the stopping time.
This is a separate branch from the potentially discontinuous zero reserve.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hneg : x + X.X (min τ T) ω < 0) :
    W (x + X.X (min τ T) ω) = 0 ∧
      ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ h : ℝ≥0, 0 < h → h < δ →
          ∃ k : ℕ,
            (X.X ((k : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((k : ℝ≥0) * h) ω) ∧
            (∀ j : ℕ, j < k →
              ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
                 upper < X.X ((j : ℝ≥0) * h) ω)) ∧
            W (x + X.X (min ((k : ℝ≥0) * h) T) ω) = 0 := by
  have hXneg : X.X (min τ T) ω ∈ Set.Iio (-x) := by
    change X.X (min τ T) ω < -x
    linarith
  have hWzero : W (x + X.X (min τ T) ω) = 0 :=
    hW.1 _ hneg
  refine ⟨hWzero, ?_⟩
  obtain ⟨δ, hδ, hmesh⟩ :=
    chat03_capped_grid_stopped_path_open_eventually
      X ω lower upper τ T hτ (Set.Iio (-x)) isOpen_Iio hXneg
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd
  obtain ⟨k, hkExit, hkfirst, hkneg⟩ := hmesh h hh hhd
  refine ⟨k, hkExit, hkfirst, ?_⟩
  have ht : X.X (min ((k : ℝ≥0) * h) T) ω < -x := by
    simpa only [Set.mem_Iio] using hkneg
  have hz : x + X.X (min ((k : ℝ≥0) * h) T) ω < 0 := by
    linarith
  exact hW.1 _ hz
