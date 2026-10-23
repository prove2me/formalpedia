-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_kernel_product_le_global_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:36:31.113131+00:00
-- url     : https://prove2.me/submissions/19cf0e01-8948-4377-84dd-0ebecc850261

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_product_le_sup_mass
import Theorems.Thm_AvramDividend_Classical_causal_nonnegative_kernel_reflected_integral_le_global

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (L D : ℝ → ℝ) (w R x : ℝ)
    (hL : IntegrableOn L (Ioi (0 : ℝ)) volume)
    (hLnonneg : ∀ u : ℝ, 0 ≤ L u)
    (hDcont : ContinuousOn D (Ioi (0 : ℝ)))
    (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R)
    (hM : BddAbove ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
      Ioc (0 : ℝ) R)) :
    (∫ s in Ioc (0 : ℝ) x,
      L (x - s) * (Real.exp (-(w * s)) * |D s|) ∂volume) ≤
    sSup ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
      Ioc (0 : ℝ) R) *
    (∫ s in Ioi (0 : ℝ), L s ∂volume) := by
  have hMnonneg :
      0 ≤ sSup ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
        Ioc (0 : ℝ) R) := by
    have hle := le_csSup hM ⟨x, hx, rfl⟩
    exact le_trans (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)) hle
  calc
    _ ≤ sSup ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
          Ioc (0 : ℝ) R) *
        (∫ s in Ioc (0 : ℝ) x, L (x - s) ∂volume) :=
      causal_weighted_kernel_product_le_sup_mass
        L D w R x hL hLnonneg hDcont hR hx hM
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (causal_nonnegative_kernel_reflected_integral_le_global
        L hL (fun t _ => hLnonneg t) x hx.1) hMnonneg
