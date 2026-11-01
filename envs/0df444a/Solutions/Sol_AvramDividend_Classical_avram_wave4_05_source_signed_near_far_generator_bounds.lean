-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_signed_near_far_generator_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:36:45.808625+00:00
-- url     : https://prove2.me/submissions/7543b5e5-00a6-4a4b-9193-df31d656c58d

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_signed_generator_residual_le_band_mass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The sharp source two-band generator estimate in the geometrically
distinct regimes 0<x<1 and x≥1. For small reserves, all jumps of size at
least one are ruin-causing. For x≥1, positive small-jump ruin overshoot is
impossible and only jumps below -x contribute to the killing bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      (if x < 1 then
        X.generator (vcstar W) x - q * vcstar W x ≤
          X.c + (X.ν).real (Ioo (-1 : ℝ) (-x)) *
            max 0 (1 - vcstar W x) -
          (X.ν).real (Iic (-1 : ℝ)) * vcstar W x - q * vcstar W x
       else
        X.generator (vcstar W) x - q * vcstar W x ≤
          X.c - (X.ν).real (Iio (-x)) * vcstar W x - q * vcstar W x) := by
  obtain ⟨hdom, hres⟩ :=
    avram_wave4_05_source_signed_generator_residual_le_band_mass
      X hX q hq W hW x hx
  refine ⟨hdom, ?_⟩
  by_cases hx1 : x < 1
  · have hLid : Iic (-1 : ℝ) ∩ Iio (-x) = Iic (-1 : ℝ) := by
      apply Set.inter_eq_left.mpr
      intro y hy
      have hyle : y ≤ -1 := hy
      have hylt : y < -x := by linarith
      exact hylt
    simpa only [if_pos hx1, hLid] using hres
  · have hxge : 1 ≤ x := le_of_not_gt hx1
    have hSempty : Ioo (-1 : ℝ) (-x) = ∅ := by
      ext y
      constructor
      · intro hy
        have hy1 : -1 < y := hy.1
        have hy2 : y < -x := hy.2
        exfalso
        linarith
      · intro hy
        exact False.elim hy
    have hLid : Iic (-1 : ℝ) ∩ Iio (-x) = Iio (-x) := by
      apply Set.inter_eq_right.mpr
      intro y hy
      have hylt : y < -x := hy
      have hy1 : y ≤ -1 := by linarith
      exact hy1
    simp only [if_neg hx1]
    simpa [hSempty, hLid] using hres
