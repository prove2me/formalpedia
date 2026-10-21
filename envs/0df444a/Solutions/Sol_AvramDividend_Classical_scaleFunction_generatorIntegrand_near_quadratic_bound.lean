-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_near_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:05:13.58001+00:00
-- url     : https://prove2.me/submissions/9ae53939-9615-4b3a-8c4e-2ac67ccfb87c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_sq_bound_near_zero_of_contDiff_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
The generator integrand of the scale function is bounded by a constant times
`y ^ 2` on a neighbourhood of the origin.

This is the Proved theorem
`scaleFunction_generatorIntegrand_sq_bound_near_zero_of_contDiff_two`
(`bd15e6f5`), with the radius stated as `r < 1` and `r < x` rather than
`r ≤ min x 1`, and with `|·|` in place of `‖·‖`; in a real normed space the
two agree.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ r < x ∧ 0 ≤ C ∧
      ∀ y ∈ Ioo (-r) 0,
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤ C * y ^ 2 := by
  obtain ⟨r, C, hr, hrC, hC, hbound⟩ :=
    scaleFunction_generatorIntegrand_sq_bound_near_zero_of_contDiff_two
      X q W hW a x hx hC2
  -- The reduced radius is the minimum of the Proved radius with the strict
  -- sub-radii `x / 2` and `1 / 2`.  It is positive, at most `r`, at most
  -- `x / 2` and at most `1 / 2`.
  have hxpos : 0 < x := hx.1
  have hxhalf : 0 < x / 2 := by positivity
  have hhalf1 : 0 < (1 : ℝ) / 2 := by norm_num
  have hr'pos : 0 < min r (min (x / 2) (1 / 2)) :=
    lt_min hr (lt_min hxhalf hhalf1)
  have hr'le_r : min r (min (x / 2) (1 / 2)) ≤ r :=
    min_le_left r (min (x / 2) (1 / 2))
  have hr'le_min : min r (min (x / 2) (1 / 2)) ≤ min (x / 2) (1 / 2) :=
    min_le_right r (min (x / 2) (1 / 2))
  have hr'le_xhalf : min (x / 2) (1 / 2) ≤ x / 2 :=
    min_le_left (x / 2) (1 / 2)
  have hr'le_half : min (x / 2) (1 / 2) ≤ 1 / 2 :=
    min_le_right (x / 2) (1 / 2)
  have hr'x : min r (min (x / 2) (1 / 2)) < x :=
    lt_of_le_of_lt (le_trans hr'le_min hr'le_xhalf) (by linarith [hxpos])
  have hr'one : min r (min (x / 2) (1 / 2)) < 1 :=
    lt_of_le_of_lt (le_trans hr'le_min hr'le_half) (by norm_num)
  refine ⟨min r (min (x / 2) (1 / 2)), C, hr'pos, hr'one, hr'x, hC, ?_⟩
  · intro y hy
    obtain ⟨hy'lo, hy'hi⟩ := Set.mem_Ioo.mp hy
    -- The new radius is at most the Proved radius, so the membership in
    -- `(-r', 0)` implies the membership in `(-r, 0)` that the Proved bound
    -- is stated for.
    have hy' : y ∈ Ioo (-r) 0 := by
      constructor
      · have hneg : -r ≤ -min r (min (x / 2) (1 / 2)) := by
          have : min r (min (x / 2) (1 / 2)) ≤ r := hr'le_r
          linarith
        exact lt_of_le_of_lt hneg hy'lo
      · exact hy'hi
    simpa only [Real.norm_eq_abs] using hbound y hy'
