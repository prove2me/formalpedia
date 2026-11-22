-- Prove2me | solution 1 for DedekindZeta.MellinPrinciple.reducedMellin_isBigO_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:47:09.817852+00:00
-- url     : https://prove2.me/submissions/1c7cebc1-91de-4285-a306-b36fee941d57

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple

set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
namespace DedekindZeta.MellinPrinciple
theorem _root_.solution (h : IsMellinPair f g a₀ b₀ C k c α) (a : ℝ) :
    (fun y : ℝ => f y - a₀) =O[atTop] (fun y : ℝ => y ^ (-a)) := by
  -- `e^{-c y^α} =o[atTop] y^{-a}` (exponential decay beats every polynomial), via
  -- `isLittleO_exp_neg_mul_rpow_atTop` composed with `y ↦ y^α → ∞`.
  have hlo : (fun y : ℝ => Real.exp (-c * y ^ α)) =o[atTop] (fun y : ℝ => y ^ (-a)) := by
    have h0 := (isLittleO_exp_neg_mul_rpow_atTop h.hc ((-a) / α)).comp_tendsto
      (tendsto_rpow_atTop h.hα)
    refine h0.congr' (Filter.EventuallyEq.rfl) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hy, mul_comm, div_mul_cancel₀ _ (ne_of_gt h.hα)]
  exact h.hf_decay.trans hlo.isBigO
end DedekindZeta.MellinPrinciple
