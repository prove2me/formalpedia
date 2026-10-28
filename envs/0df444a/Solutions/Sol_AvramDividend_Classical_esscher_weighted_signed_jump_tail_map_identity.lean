-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_signed_jump_tail_map_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:06:50.440951+00:00
-- url     : https://prove2.me/submissions/79e4a500-4a86-4633-b43e-d6cfbd8f0fc5

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- The Esscher-weighted tail of positive jump magnitudes is the strict
    signed negative-jump tail after the measurable reflection map. -/
theorem solution
    (ν : Measure ℝ) (φ r : ℝ) (hr : 0 < r) :
    ((ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
        {z : ℝ≥0 | r < (z : ℝ)} =
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
      (Iio (-r)) := by
  let g : ℝ → ℝ≥0 := fun y => Real.toNNReal (-y)
  let s : Set ℝ≥0 := {z | r < (z : ℝ)}
  have hs : MeasurableSet s := by
    change MeasurableSet ((fun z : ℝ≥0 => (z : ℝ)) ⁻¹' Ioi r)
    exact measurableSet_Ioi.preimage measurable_coe_nnreal_real
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hiff (y : ℝ) : r < (g y : ℝ) ↔ y < -r := by
    constructor
    · intro h
      by_cases hy : 0 ≤ -y
      · rw [show (g y : ℝ) = -y from Real.coe_toNNReal (-y) hy] at h
        linarith
      · have hy0 : -y ≤ 0 := le_of_lt (lt_of_not_ge hy)
        have hz : g y = 0 := Real.toNNReal_of_nonpos hy0
        rw [hz] at h
        have hbad : r < (0 : ℝ) := by simpa using h
        exact False.elim ((not_lt_of_ge hr.le) hbad)
    · intro h
      have hy0 : 0 ≤ -y := by linarith
      rw [show (g y : ℝ) = -y from Real.coe_toNNReal (-y) hy0]
      linarith
  have hpre : g ⁻¹' s = Iio (-r) := by
    ext y
    change (r < (g y : ℝ)) ↔ y < -r
    exact hiff y
  have hweight : EqOn
      (fun y : ℝ => ENNReal.ofReal (Real.exp (-(φ * (g y : ℝ)))))
      (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))
      (Iio (-r)) := by
    intro y hy
    have hy0 : 0 ≤ -y := by
      have : y < -r := hy
      linarith
    change ENNReal.ofReal (Real.exp (-(φ * (g y : ℝ)))) =
      ENNReal.ofReal (Real.exp (φ * y))
    rw [show (g y : ℝ) = -y from Real.coe_toNNReal (-y) hy0]
    congr 2
    ring
  have hf : Measurable (fun z : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) := by
    have hc : Continuous (fun z : ℝ≥0 => -(φ * (z : ℝ))) := by
      fun_prop
    have he : Measurable (fun z : ℝ≥0 => Real.exp (-(φ * (z : ℝ)))) :=
      (Real.continuous_exp.comp hc).measurable
    exact he.ennreal_ofReal
  calc
    ((ν.map g).withDensity
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))) s
        = ∫⁻ z in s, ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) ∂(ν.map g) := by
            rw [withDensity_apply _ hs]
    _ = ∫⁻ y in Iio (-r), ENNReal.ofReal (Real.exp (-(φ * (g y : ℝ)))) ∂ν := by
          rw [setLIntegral_map hs hf hg, hpre]
    _ = ∫⁻ y in Iio (-r), ENNReal.ofReal (Real.exp (φ * y)) ∂ν :=
          setLIntegral_congr_fun measurableSet_Iio hweight
    _ = (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
          (Iio (-r)) := by
          rw [withDensity_apply _ measurableSet_Iio]
