-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_strict_lower_exit_no_creeping_ae_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:31:37.148903+00:00
-- url     : https://prove2.me/submissions/27369e20-71d7-4765-9a74-7451719eabd7

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_choose_finite_mesh_horizon_indices_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_capped_lower_clock_zero_dyadic_slope_ae_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_reciprocal_dyadic_mesh_cover_ws01c
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_strict_lower_exit_no_creeping_of_cap_slopes_no_standing_public

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) <
        ⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞) →
      x + X.X (⨅ (t : ℝ≥0) (_ : X.X t ω < -x),
        (t : ℝ≥0∞)).toNNReal ω ≠ 0 := by
  let δ : ℕ → ℝ≥0 := fun n => ((1 : ℝ≥0) / 2) ^ n
  have hPos : ∀ n : ℕ, 0 < δ n := by
    intro n
    dsimp [δ]
    positivity
  have hZero : Tendsto δ atTop (𝓝 (0 : ℝ≥0)) := by
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1 : ℝ≥0) / 2 < 1)
  have hRatio : ∀ n, (δ n : ℝ) ≤
      2 * (δ (n + 1) : ℝ) := by
    intro n
    dsimp [δ]
    rw [pow_succ]
    norm_num [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div]
    apply le_of_eq
    ring
  have hDyadicCover :
      ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
        ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n := by
    intro N t ht htN
    exact bv_reciprocal_dyadic_mesh_cover_ws01c N t ht htN
  have hCapSlope : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X (((twoSidedExitDownTime X (-x) ω) ⊓
              (N : ℝ≥0∞)).toNNReal + δ n) ω -
            X.X (((twoSidedExitDownTime X (-x) ω) ⊓
              (N : ℝ≥0∞)).toNNReal) ω)) /
          (δ n : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
    intro N
    obtain ⟨M, hM⟩ :=
      bv_choose_finite_mesh_horizon_indices_ws01c
        (N : ℝ≥0) δ hPos
    have hCapped :=
      bv_capped_lower_clock_zero_dyadic_slope_ae_ws01c
        X hBV (-x) (N : ℝ≥0) δ M hPos hZero hM
    simpa only [δ, ENNReal.coe_natCast] using hCapped
  have hNoCreep :=
    p2m81_bv_strict_lower_exit_no_creeping_of_cap_slopes_no_standing_public
      X q φ hq hφ hroot hBV a x δ hPos hRatio hDyadicCover hCapSlope
  simpa only [twoSidedExitDownTime, twoSidedExitUpTime] using hNoCreep
