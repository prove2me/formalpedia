-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_tilted_scale_locally_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:13:09.938711+00:00
-- url     : https://prove2.me/submissions/562e1e8c-b7d3-4ebc-b611-887fe55f93f1

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Group.Abs
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The zero-origin monotone Gaussian scale function bounds its Esscher tilt. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C := by
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hmono : Monotone W := scaleFunction_monotone X q W hW
  intro R hR
  refine ⟨W R, ?_⟩
  intro x hx
  have hWx_nonneg : 0 ≤ W x := by
    simpa [hzero] using hmono (le_of_lt hx.1)
  have hWx_le : W x ≤ W R := hmono hx.2
  have hφx : 0 ≤ φ * x :=
    mul_nonneg hφ.le (le_of_lt hx.1)
  have he_le : Real.exp (-(φ * x)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hφx)
  rw [hV x hx.1, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hWx_nonneg)]
  calc
    Real.exp (-(φ * x)) * W x ≤ 1 * W x :=
      mul_le_mul_of_nonneg_right he_le hWx_nonneg
    _ = W x := one_mul _
    _ ≤ W R := hWx_le
