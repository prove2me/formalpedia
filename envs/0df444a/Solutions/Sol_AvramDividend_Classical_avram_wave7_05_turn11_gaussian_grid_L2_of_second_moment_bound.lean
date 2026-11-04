-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn11_gaussian_grid_L2_of_second_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:49:20.43321+00:00
-- url     : https://prove2.me/submissions/479aea62-9f07-4970-b885-cea2b8e8b587

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology
noncomputable section

/-! Turn an exact finite-mesh second-moment bound into the Vitali L² norm bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : MemLp f 2 P)
    (hMoment : (∫ ω, (f ω) ^ 2 ∂P) ≤ B) :
    eLpNorm f (2 : ℝ≥0∞) P ≤
      ENNReal.ofReal (Real.sqrt B) := by
  have hIntNonneg : 0 ≤ (∫ ω, (f ω) ^ 2 ∂P) :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hL : eLpNorm f (2 : ℝ≥0∞) P =
      ENNReal.ofReal
        ((∫ ω, (f ω) ^ 2 ∂P) ^ ((2 : ℝ)⁻¹)) := by
    have hh (ω : Ω) :
        ‖f ω‖ ^ (2 : ℝ≥0∞).toReal = (f ω) ^ 2 := by
      calc
        ‖f ω‖ ^ (2 : ℝ≥0∞).toReal =
            ‖f ω‖ ^ ((2 : ℕ) : ℝ) := by norm_num
        _ = ‖f ω‖ ^ (2 : ℕ) := by rw [Real.rpow_natCast]
        _ = (f ω) ^ 2 := by
          simpa only [Real.norm_eq_abs] using (sq_abs (f ω))
    have hEq :
        (∫ ω, ‖f ω‖ ^ (2 : ℝ≥0∞).toReal ∂P) =
          (∫ ω, (f ω) ^ 2 ∂P) :=
      integral_congr_ae (Filter.Eventually.of_forall hh)
    calc
      eLpNorm f (2 : ℝ≥0∞) P =
          ENNReal.ofReal
            ((∫ ω, ‖f ω‖ ^ (2 : ℝ≥0∞).toReal ∂P) ^
              ((2 : ℝ≥0∞).toReal)⁻¹) :=
        hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      _ = ENNReal.ofReal
            ((∫ ω, (f ω) ^ 2 ∂P) ^ ((2 : ℝ)⁻¹)) := by
        rw [hEq]
        norm_num
  rw [hL]
  have hRoot : (∫ ω, (f ω) ^ 2 ∂P) ^ ((2 : ℝ)⁻¹) ≤
      B ^ ((2 : ℝ)⁻¹) :=
    Real.rpow_le_rpow hIntNonneg hMoment (by norm_num)
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.sqrt_eq_rpow, one_div] using hRoot
