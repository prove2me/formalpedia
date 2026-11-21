-- Prove2me | solution 1 for AvramDividend.Classical.avram_a30_original_discount_weighted_nonnegative_L1_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:42:18.026288+00:00
-- url     : https://prove2.me/submissions/4d3cff93-e47f-4946-9c6f-41cbb1a69d30

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F E : ℕ → Ω → ℝ)
    (hFI : ∀ m, Integrable (F m) P)
    (hFpos : ∀ m, ∀ᵐ ω ∂P, 0 ≤ F m ω)
    (hEm : ∀ m, AEStronglyMeasurable (E m) P)
    (hEb : ∀ m, ∀ᵐ ω ∂P, 0 ≤ E m ω ∧ E m ω ≤ 1)
    (hLimit : Tendsto (fun m => ∫ ω, F m ω ∂P)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, E m ω * F m ω ∂P)
      atTop (nhds (0 : ℝ))  := by
  have hWI : ∀ m, Integrable (fun ω => E m ω * F m ω) P := by
    intro m
    have hm : AEStronglyMeasurable
        (fun ω => E m ω * F m ω) P :=
      (hEm m).mul (hFI m).aestronglyMeasurable
    refine (hFI m).mono' hm ?_
    filter_upwards [hEb m, hFpos m] with ω hE hF
    have hmul : E m ω * F m ω ≤ F m ω := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hE.2) hF]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hE.1 hF)] using hmul
  have hLower (m : ℕ) :
      0 ≤ ∫ ω, E m ω * F m ω ∂P :=
    integral_nonneg_of_ae (by
      filter_upwards [hEb m, hFpos m] with ω he hf
      exact mul_nonneg he.1 hf)
  have hUpper (m : ℕ) :
      (∫ ω, E m ω * F m ω ∂P) ≤ (∫ ω, F m ω ∂P) :=
    integral_mono_ae (hWI m) (hFI m) (by
      filter_upwards [hEb m, hFpos m] with ω he hf
      nlinarith [mul_nonneg (sub_nonneg.mpr he.2) hf])
  exact squeeze_zero hLower hUpper hLimit
