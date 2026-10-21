-- Prove2me | solution 1 for AvramDividend.Classical.chat03_grid_upperfirst_weight_tendsto_on_upperfirst
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:17:36.410743+00:00
-- url     : https://prove2.me/submissions/47310328-4ba9-4014-83e2-49b887fdafce

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal

/-!
At a strict upper-first limiting passage the exact grid discount
converges, including the case of an infinite losing lower clock.
-/
theorem solution
    (q : ℝ) (up down : ℝ≥0∞)
    (upGrid downGrid : ℕ → ℝ≥0∞)
    (hu : Tendsto upGrid atTop (𝓝 up))
    (hd : Tendsto downGrid atTop (𝓝 down))
    (hupper : up < down) :
    Tendsto
      (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n))))
        else 0) atTop
      (𝓝 (ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal up))))) := by
  have hfinite : up ≠ ∞ := ne_top_of_lt hupper
  have hto : Tendsto
      (fun n => ENNReal.toReal (upGrid n)) atTop
      (𝓝 (ENNReal.toReal up)) :=
    (ENNReal.continuousAt_toReal hfinite).tendsto.comp hu
  have hcontinuous : Continuous (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * t)))) :=
    ENNReal.continuous_ofReal.comp
      ((Real.continuous_exp).comp
        ((continuous_const.mul continuous_id).neg))
  have hdiscount : Tendsto
      (fun n => ENNReal.ofReal (Real.exp
        (-(q * ENNReal.toReal (upGrid n)))))
      atTop
      (𝓝 (ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal up))))) :=
    (hcontinuous.tendsto (ENNReal.toReal up)).comp hto
  have hstrict : ∀ᶠ n in atTop, upGrid n < downGrid n :=
    Filter.Tendsto.eventually_lt hu hd hupper
  have hEq :
      (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n))))
        else 0) =ᶠ[atTop]
      (fun n => ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (upGrid n))))) := by
    filter_upwards [hstrict] with n hn
    simp [hn]
  exact hdiscount.congr' hEq.symm
