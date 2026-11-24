-- Prove2me | solution 2 for GaussianPerimeter.VolumeComparison.weighted_amgm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:20:54.147716+00:00
-- url     : https://prove2.me/submissions/04513d2f-09ff-4f89-9d1d-1146d39702a3

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution {θ a b : ℝ} (hθ : 0 < θ ∧ θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    : ((1-θ)^(1-θ) * θ^θ)⁻¹ * a^(1-θ) * b^θ ≤ a + b := calc
  ((1-θ)^(1-θ) * θ^θ)⁻¹ * a^(1-θ) * b^θ = ((1-θ)^(1-θ))⁻¹ * a^(1-θ) * (θ^θ)⁻¹ * b^θ := by grind
  _ = ((1-θ)⁻¹)^(1-θ) * a^(1-θ) * (θ⁻¹)^θ * b^θ := by
    rw [Real.inv_rpow (by linarith), Real.inv_rpow (by linarith)]
  _ = ((1-θ)⁻¹*a)^(1-θ) * (θ⁻¹*b)^θ := by
    rw [Real.mul_rpow (by simp only [inv_nonneg, sub_nonneg]; linarith) ha,
      Real.mul_rpow (by simp only [inv_nonneg]; linarith) hb]
    ring
  _ ≤ (1-θ)*((1-θ)⁻¹*a) + θ*(θ⁻¹*b) :=
    Real.geom_mean_le_arith_mean2_weighted
      (by linarith) (by linarith) (by simp [hθ.2, ha]) (by simp [hθ.1, hb]) (by ring)
  _ = a + b := by grind
end GaussianPerimeter.VolumeComparison
