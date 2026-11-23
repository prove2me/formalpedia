-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_real_second_moment_eventual_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:20:49.074709+00:00
-- url     : https://prove2.me/submissions/a29480fa-6f1c-49c8-b0cd-1b6052af0999

import Mathlib.MeasureTheory.Function.L2Space
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_eventual_l2_mass_expectations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- A finite exceptional prefix does not affect convergence of genuine expectations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (C : ℝ) (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hi : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hC : 0 ≤ C)
    (hbound : ∀ n, N ≤ n → (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ C)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by
  let B : ℝ≥0 := NNReal.mk (C ^ (1 / 2 : ℝ)) (Real.rpow_nonneg hC _)
  have hL2 (n : ℕ) (hn : N ≤ n) :
      eLpNorm (Y n) 2 μ ≤ (B : ENNReal) := by
    have hMem : MemLp (Y n) 2 μ :=
      (memLp_two_iff_integrable_sq (hm n)).2 (hi n)
    have hFormula := hMem.eLpNorm_eq_integral_rpow_norm
      (show (2 : ENNReal) ≠ 0 by norm_num)
      (show (2 : ENNReal) ≠ ⊤ by norm_num)
    have hSquare :
        (fun ω => ‖Y n ω‖ ^ ((2 : ENNReal).toReal)) =
        (fun ω => (Y n ω) ^ 2) := by
      funext ω
      simp [Real.norm_eq_abs, Real.rpow_natCast, sq_abs]
    have hFormula' :
        eLpNorm (Y n) 2 μ =
          ENNReal.ofReal ((∫ ω, (Y n ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
      simpa [hSquare, one_div] using hFormula
    have hnonneg : 0 ≤ (∫ ω, (Y n ω) ^ 2 ∂μ) :=
      integral_nonneg (fun ω => sq_nonneg (Y n ω))
    calc
      eLpNorm (Y n) 2 μ =
          ENNReal.ofReal ((∫ ω, (Y n ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := hFormula'
      _ ≤ ENNReal.ofReal (C ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow hnonneg (hbound n hn) (by norm_num))
      _ = (B : ENNReal) := by
        simpa only [B] using
          (ENNReal.ofReal_eq_coe_nnreal (Real.rpow_nonneg hC (1 / 2 : ℝ)))
  have hMass : (μ Set.univ) ^ (1 / 2 : ℝ) ≤ (1 : ENNReal) := by simp
  exact avram_p2_j_ui_finite_measure_eventual_l2_mass_expectations
    μ Y Z B 1 N hm hL2 hMass hae
