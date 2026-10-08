-- Prove2me | solution 2 for AvramDividend.Classical.zero_cap_value_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:01:03.177346+00:00
-- url     : https://prove2.me/submissions/330d0d42-73e2-4f6a-a12b-48a6b59e7843
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_boundary_value_package
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  rcases zero_cap_boundary_value_package X hX q hq W hW with
    ⟨hbar0, hbound0⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simpa using hbound0
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hsplit :
        valueFunctionLe X q 0 x =
          ENNReal.ofReal x + valueFunctionLe X q 0 0 := by
      simpa using valueFunctionLe_above_cap X q x 0 (le_refl 0) hxpos
    have hbarrier :
        barrierValue W 0 x = x + barrierValue W 0 0 := by
      simp [barrierValue, not_lt.mpr hx, not_le.mpr hxpos]
    calc
      valueFunctionLe X q 0 x
          = ENNReal.ofReal x + valueFunctionLe X q 0 0 := hsplit
      _ ≤ ENNReal.ofReal x + ENNReal.ofReal (barrierValue W 0 0) :=
        by
          simpa only [add_comm] using
            add_le_add_left hbound0 (ENNReal.ofReal x)
      _ = ENNReal.ofReal (x + barrierValue W 0 0) := by
        symm
        exact ENNReal.ofReal_add hx hbar0
      _ = ENNReal.ofReal (barrierValue W 0 x) := by rw [hbarrier]
