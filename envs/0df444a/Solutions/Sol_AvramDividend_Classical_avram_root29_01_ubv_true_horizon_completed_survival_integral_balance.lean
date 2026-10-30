-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_ubv_true_horizon_completed_survival_integral_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:28:51.94835+00:00
-- url     : https://prove2.me/submissions/7fb4fef9-4e2c-400b-9a42-3f73241a32c9

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_genuine_finite_horizon_killed_expectation_no_mesh
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_horizon_killed_reward_two_way_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Actual UBV completed-upper plus surviving-horizon reward integrates exactly to Wq(x). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
    (let S : Ω → ℝ := fun ω =>
      let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
      let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
      (if U < D ∧ U.toNNReal ≤ T then
        Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
      else 0) +
      (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
        Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else 0);
    Integrable S P ∧ (∫ ω, S ω ∂P) = W x) := by
  let Z : Ω → ℝ := fun ω =>
    if (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
      if min (twoSidedExitUpTime X (a-x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min (min
          (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min (min
            (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
    else if twoSidedExitDownTime X (-x) ω <
            twoSidedExitUpTime X (a-x) ω then 0
    else Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
      W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
  let S : Ω → ℝ := fun ω =>
    let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
    let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
    (if U < D ∧ U.toNNReal ≤ T then
      Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
    else 0) +
    (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
      Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
    else 0)
  have hZS : Z = S := by
    funext ω
    exact avram_ws01b_actual_horizon_killed_reward_two_way_split
      X q W a x ha hxa T ω
  have hInt := avram_root29_01_ubv_genuine_finite_horizon_killed_expectation_no_mesh
    X hnbv q hq W hW a x ha hx0 hxa T
  change Integrable Z P ∧ (∫ ω, Z ω ∂P) = W x at hInt
  rw [hZS] at hInt
  exact hInt
