-- Prove2me | solution 1 for AvramDividend.Classical.bv_strict_lower_exit_no_creeping_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:41:59.989509+00:00
-- url     : https://prove2.me/submissions/ebd8279a-c427-4b1c-9f1a-ba2e2008cc6e

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_choose_finite_mesh_horizon_indices_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_capped_lower_clock_zero_dyadic_slope_ae_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_reciprocal_dyadic_mesh_cover_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_no_creeping_of_all_capped_zero_slopes_ws01c

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-!
WS01C canonical no-creeping assembly from the actual capped-clock
dyadic slope law and the Proved all-cap no-creeping theorem.
The exact canonical target can be submitted through the guarded
standalone UUID-bound route once the final helper import is Proved.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
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
    bv_no_creeping_of_all_capped_zero_slopes_ws01c
      X hX hBV a x δ hPos hRatio hDyadicCover hCapSlope
  simpa only [twoSidedExitDownTime, twoSidedExitUpTime] using hNoCreep