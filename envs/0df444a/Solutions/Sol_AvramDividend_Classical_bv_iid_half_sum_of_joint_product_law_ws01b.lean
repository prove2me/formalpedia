-- Prove2me | solution 1 for AvramDividend.Classical.bv_iid_half_sum_of_joint_product_law_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:26:12.815281+00:00
-- url     : https://prove2.me/submissions/58adaa57-0a42-4115-ab30-17b63c7a56c5

import Theorems.Thm_AvramDividend_Classical_bv_iid_pair_half_sum_weighted_integral_ws01b
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical

/-- Pull a product-law exchangeability identity back to sample paths. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Measure ℝ) [SFinite μ]
    (pair : Ω → ℝ × ℝ)
    (hPairMeas : AEMeasurable pair P)
    (hJoint : Measure.map pair P = μ.prod μ)
    (g : ℝ → ℝ)
    (hFirst : Integrable
      (fun z : ℝ × ℝ => z.1 * g (z.1 + z.2)) (μ.prod μ))
    (hSecond : Integrable
      (fun z : ℝ × ℝ => z.2 * g (z.1 + z.2)) (μ.prod μ)) :
    2 * (∫ ω, (pair ω).1 * g ((pair ω).1 + (pair ω).2) ∂P) =
      ∫ ω, ((pair ω).1 + (pair ω).2) *
        g ((pair ω).1 + (pair ω).2) ∂P := by
  have hTotal : Integrable
      (fun z : ℝ × ℝ =>
        (z.1 + z.2) * g (z.1 + z.2)) (μ.prod μ) := by
    have hEq :
        (fun z : ℝ × ℝ =>
          (z.1 + z.2) * g (z.1 + z.2)) =
        (fun z : ℝ × ℝ => z.1 * g (z.1 + z.2)) +
          (fun z : ℝ × ℝ => z.2 * g (z.1 + z.2)) := by
      funext z
      simp only [Pi.add_apply, add_mul]
    rw [hEq]
    exact hFirst.add hSecond
  have hFirstMap :
      (∫ z : ℝ × ℝ, z.1 * g (z.1 + z.2) ∂(μ.prod μ)) =
      ∫ ω, (pair ω).1 * g ((pair ω).1 + (pair ω).2) ∂P := by
    simpa only [hJoint, Function.comp_def] using
      (integral_map hPairMeas (by simpa only [hJoint] using hFirst.aestronglyMeasurable))
  have hTotalMap :
      (∫ z : ℝ × ℝ,
        (z.1 + z.2) * g (z.1 + z.2) ∂(μ.prod μ)) =
      ∫ ω, ((pair ω).1 + (pair ω).2) *
        g ((pair ω).1 + (pair ω).2) ∂P := by
    simpa only [hJoint, Function.comp_def] using
      (integral_map hPairMeas (by simpa only [hJoint] using hTotal.aestronglyMeasurable))
  calc
    2 * (∫ ω, (pair ω).1 * g ((pair ω).1 + (pair ω).2) ∂P) =
      2 * (∫ z : ℝ × ℝ, z.1 * g (z.1 + z.2) ∂(μ.prod μ)) := by
        rw [hFirstMap]
    _ = ∫ z : ℝ × ℝ, (z.1 + z.2) * g (z.1 + z.2) ∂(μ.prod μ) :=
      bv_iid_pair_half_sum_weighted_integral_ws01b μ g hFirst hSecond
    _ = ∫ ω, ((pair ω).1 + (pair ω).2) *
        g ((pair ω).1 + (pair ω).2) ∂P := hTotalMap
