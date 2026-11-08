-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux20_original_unit_strict_product_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:53:39.264623+00:00
-- url     : https://prove2.me/submissions/86ff10d6-b5d8-42fe-99cd-667ec44e00d7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_original_unit_shortcell_power
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_original_shortcell_product_quadratic
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_quadratic_shortcell_power_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Recover the exact original marked-jump Laplace law from source-exact
    short-cell product independence, collision estimates, and the power limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k : ℕ) :
    (∫ ω : Ω, ∏ u ∈
      (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) =
    Real.exp (-(∫ y in Iio (-(1 / ((k : ℝ) + 1))),
      (1 - Real.exp y) ∂X.ν)) := by
  let U : ℝ := (∫ ω : Ω, ∏ u ∈
      (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 : ℝ≥0) k).toFinset,
      Real.exp (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P)
  let q : ℕ → ℝ := fun n =>
    (∫ ω : Ω, ∏ u ∈
      (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 / ((n : ℝ≥0) + 1)) k).toFinset,
      Real.exp (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P)
  let a : ℝ := ∫ y in Iio (-(1 / ((k : ℝ) + 1))),
      (1 - Real.exp y) ∂X.ν
  let C : ℝ := (X.ν (Iic (-(1 / ((k : ℝ) + 1))))).toReal ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  have hquadratic (n : ℕ) :
      0 ≤ q n ∧ q n ≤ 1 ∧
      0 ≤ q n - (1 - a / ((n + 1 : ℕ) : ℝ)) ∧
      q n - (1 - a / ((n + 1 : ℕ) : ℝ)) ≤
        C / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    simpa only [q, a, C] using
      (avram_bv_jump8_turn10_original_shortcell_product_quadratic
        X hX hBV k n)
  have hlim : Tendsto (fun n : ℕ => (q n) ^ (n + 1))
      atTop (𝓝 (Real.exp (-a))) :=
    avram_bv_jump8_turn10_quadratic_shortcell_power_limit
      a C q hC
      (fun n => ⟨(hquadratic n).1, (hquadratic n).2.1⟩)
      (fun n => ⟨(hquadratic n).2.2.1, (hquadratic n).2.2.2⟩)
  have hfactor (n : ℕ) : U = q n ^ (n + 1) := by
    simpa only [U, q] using
      (avram_bv_jump8_turn10_original_unit_shortcell_power
        X hX hBV k n)
  have hconst : Tendsto (fun _ : ℕ => U) atTop
      (𝓝 (Real.exp (-a))) := by
    convert hlim using 1
    funext n
    exact hfactor n
  have huniq : U = Real.exp (-a) :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  simpa only [U, a] using huniq
