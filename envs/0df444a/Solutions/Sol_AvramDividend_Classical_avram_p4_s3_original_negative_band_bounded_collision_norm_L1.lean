-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_collision_norm_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:02:22.689628+00:00
-- url     : https://prove2.me/submissions/c5469dc5-14c2-4128-8d7e-add2ba406d32

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_bounded_weighted_collision_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (H : Ω → ℝ) (hHm : Measurable H) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ ω, |H ω| ≤ B) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0)) P ∧
    (∫ ω, ‖H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0)‖ ∂P) ≤ B * r ^ 2 := by
  classical
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let J : Ω → ℝ := fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0
  change Integrable (fun ω => H ω * J ω) P ∧
    (∫ ω, ‖H ω * J ω‖ ∂P) ≤ B * r ^ 2
  have hWeighted :=
    avram_p4_s3_original_negative_band_bounded_weighted_collision_L1
      X T n H hHm B hB hH
  change Integrable (fun ω => H ω * J ω) P ∧
    |∫ ω, H ω * J ω ∂P| ≤ B * r ^ 2 at hWeighted
  have hAbsBound (ω : Ω) : abs (abs (H ω)) ≤ B := by
    simpa only [abs_abs] using hH ω
  have hAbs :=
    avram_p4_s3_original_negative_band_bounded_weighted_collision_L1
      X T n (fun ω => |H ω|) hHm.abs B hB hAbsBound
  change Integrable (fun ω => |H ω| * J ω) P ∧
    |∫ ω, |H ω| * J ω ∂P| ≤ B * r ^ 2 at hAbs
  have hJnn (ω : Ω) : 0 ≤ J ω := by
    dsimp [J]
    split_ifs <;> positivity
  have hNormEq (ω : Ω) : ‖H ω * J ω‖ = |H ω| * J ω := by
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn ω)]
  have hNormFun : (fun ω => ‖H ω * J ω‖) =
      (fun ω => |H ω| * J ω) := funext hNormEq
  have hPos (ω : Ω) : 0 ≤ |H ω| * J ω :=
    mul_nonneg (abs_nonneg _) (hJnn ω)
  have hMeanNN : 0 ≤ ∫ ω, |H ω| * J ω ∂P :=
    integral_nonneg hPos
  refine ⟨hWeighted.1, ?_⟩
  rw [hNormFun]
  calc
    (∫ ω, |H ω| * J ω ∂P) =
        |∫ ω, |H ω| * J ω ∂P| := (abs_of_nonneg hMeanNN).symm
    _ ≤ B * r ^ 2 := hAbs.2
