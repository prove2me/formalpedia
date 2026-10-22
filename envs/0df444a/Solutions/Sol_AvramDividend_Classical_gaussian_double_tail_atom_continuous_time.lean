-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_atom_continuous_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:15:11.946324+00:00
-- url     : https://prove2.me/submissions/fef642b1-450b-4b99-be19-5533a841aca6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal

/-- Each Gaussian Esscher double-tail atom is continuous at positive times. -/
theorem solution (φ z t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun u : ℝ =>
      if 0 < u ∧ u < z then
        ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))
      else 0) t := by
  have hrepr (u : ℝ) (hu : 0 < u) :
      (if 0 < u ∧ u < z then
        ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) =
      ENNReal.ofReal (max (z - u) 0) *
        ENNReal.ofReal (Real.exp (-φ * z)) := by
    by_cases huz : u < z
    · have hnonneg : 0 ≤ z - u := sub_nonneg.mpr huz.le
      simp [hu, huz, max_eq_left hnonneg]
    · have hnonpos : z - u ≤ 0 := sub_nonpos.mpr (le_of_not_gt huz)
      simp [hu, huz, max_eq_right hnonpos]
  have hreal : Continuous
      (fun u : ℝ => max (z - u) 0 * Real.exp (-φ * z)) := by
    fun_prop
  have henreal : Continuous
      (fun u : ℝ => ENNReal.ofReal (max (z - u) 0 * Real.exp (-φ * z))) :=
    ENNReal.continuous_ofReal.comp hreal
  have hcont : ContinuousAt
      (fun u : ℝ => ENNReal.ofReal (max (z - u) 0) *
        ENNReal.ofReal (Real.exp (-φ * z))) t := by
    have hfun : (fun u : ℝ => ENNReal.ofReal (max (z - u) 0) *
        ENNReal.ofReal (Real.exp (-φ * z))) =
        (fun u : ℝ => ENNReal.ofReal
          (max (z - u) 0 * Real.exp (-φ * z))) := by
      funext u
      exact (ENNReal.ofReal_mul (le_max_right (z - u) 0)).symm
    rw [hfun]
    exact henreal.continuousAt
  change Tendsto
    (fun u : ℝ =>
      if 0 < u ∧ u < z then
        ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))
      else 0) (𝓝 t)
    (𝓝 (if 0 < t ∧ t < z then
      ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
      else 0))
  rw [hrepr t ht]
  exact Filter.Tendsto.congr'
    (Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht)
      (fun u hu => (hrepr u hu).symm))
    hcont
