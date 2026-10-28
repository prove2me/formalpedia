-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_monotone_of_zero_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:05:29.261917+00:00
-- url     : https://prove2.me/submissions/a7424b27-9468-4f2f-91b8-52fe14861029

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A nonnegative value at the zero barrier glues the zero branch for
negative reserves to the unit-slope affine branch for nonnegative reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc0 : cstar W = 0) :
    Monotone (vcstar W) := by
  have hzero : 0 ≤ barrierValue W 0 0 :=
    barrierValue_nonnegative_for_nonnegative_capital
      X hX q hq W hW 0 0 le_rfl le_rfl
  have hneg : ∀ z : ℝ, z < 0 → barrierValue W 0 z = 0 := by
    intro z hz
    simp [barrierValue, hz]
  have hmono : Monotone (barrierValue W 0) := by
    intro x y hxy
    by_cases hyneg : y < 0
    · have hxneg : x < 0 := lt_of_le_of_lt hxy hyneg
      rw [hneg x hxneg, hneg y hyneg]
    · have hy : 0 ≤ y := le_of_not_gt hyneg
      by_cases hxneg : x < 0
      · rw [hneg x hxneg, barrierValue_zero_affine_nonnegative W y hy]
        linarith
      · have hx : 0 ≤ x := le_of_not_gt hxneg
        rw [barrierValue_zero_affine_nonnegative W x hx,
            barrierValue_zero_affine_nonnegative W y hy]
        linarith
  change Monotone (barrierValue W (cstar W).toReal)
  simpa [hc0] using hmono
