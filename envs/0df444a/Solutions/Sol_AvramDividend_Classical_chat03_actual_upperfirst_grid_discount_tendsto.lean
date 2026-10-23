-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_upperfirst_grid_discount_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:49:42.847647+00:00
-- url     : https://prove2.me/submissions/3e443c0e-e829-40c0-b806-503afbfae3af

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_upper_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_official_lower_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_official_no_upper_exit_grid_inf_top
import Theorems.Thm_AvramDividend_Classical_chat03_official_grid_discount_tendsto_from_clock_convergence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (hsep : lower < upper)
    (q : ℝ) (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n =>
        if (⨅ k : ℕ,
          if upper < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
          else ∞) <
          (⨅ k : ℕ,
            if X.X ((k : ℝ≥0) * mesh n) ω < lower then
              (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
            else ∞) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ k : ℕ,
              if upper < X.X ((k : ℝ≥0) * mesh n) ω then
                (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
              else ∞))))
        else 0) atTop
      (𝓝 (if twoSidedExitUpTime X upper ω <
          twoSidedExitDownTime X lower ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))
        else 0)) := by
  let upGrid : ℕ → ℝ≥0∞ := fun n =>
    ⨅ k : ℕ,
      if upper < X.X ((k : ℝ≥0) * mesh n) ω then
        (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
      else ∞
  let downGrid : ℕ → ℝ≥0∞ := fun n =>
    ⨅ k : ℕ,
      if X.X ((k : ℝ≥0) * mesh n) ω < lower then
        (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
      else ∞
  have hu : Tendsto upGrid atTop
      (𝓝 (twoSidedExitUpTime X upper ω)) :=
    chat03_official_upper_grid_clock_tendsto
      X ω upper mesh hpos hzero
  have hd : Tendsto downGrid atTop
      (𝓝 (twoSidedExitDownTime X lower ω)) :=
    chat03_official_lower_grid_clock_tendsto
      X ω lower mesh hpos hzero
  have hNo : twoSidedExitUpTime X upper ω = ∞ →
      ∀ n : ℕ, upGrid n = ∞ := by
    intro hinf n
    exact chat03_official_no_upper_exit_grid_inf_top
      X ω upper (mesh n) hinf
  exact chat03_official_grid_discount_tendsto_from_clock_convergence
    X ω lower upper hsep q upGrid downGrid hu hd hNo
