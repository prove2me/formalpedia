-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_convolution_abs_le_finite_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:22:50.260467+00:00
-- url     : https://prove2.me/submissions/ded15fb0-e0ad-4655-aad2-7ff374953405

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_locally_bounded_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_bddAbove_of_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_product_le_sup_mass
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C)
    (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R) :
    |∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume| ≤
      sSup ((fun s : ℝ => |V s|) '' Ioc (0 : ℝ) R) *
        (∫ s in Ioc (0 : ℝ) x, |K s| ∂volume) := by
  have hLi : IntegrableOn (fun t : ℝ => |K t|)
      (Ioi (0 : ℝ)) volume := by
    change Integrable (fun t : ℝ => |K t|)
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [Real.norm_eq_abs] using hK.norm
  have hLn : ∀ t : ℝ, 0 ≤ |K t| := fun t => abs_nonneg _
  have hMb' := causal_weighted_sup_bddAbove_of_locally_bounded
    V 0 (le_refl (0 : ℝ)) hVb R hR
  have hMb : BddAbove ((fun t : ℝ => |V t|) '' Ioc (0 : ℝ) R) := by
    simpa only [zero_mul, neg_zero, Real.exp_zero, one_mul] using hMb'
  have hp' := causal_weighted_kernel_product_le_sup_mass
    (fun t : ℝ => |K t|) V 0 R x hLi hLn hVc hR hx hMb'
  have hp :
      (∫ s in Ioc (0 : ℝ) x, |K (x - s)| * |V s| ∂volume) ≤
      sSup ((fun s : ℝ => |V s|) '' Ioc (0 : ℝ) R) *
        (∫ s in Ioc (0 : ℝ) x, |K (x - s)| ∂volume) := by
    simpa only [zero_mul, neg_zero, Real.exp_zero, one_mul] using hp'
  have hRev :
      (∫ s in Ioc (0 : ℝ) x, |K (x - s)| ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, |K s| ∂volume) := by
    simpa only [mul_one] using
      (causal_convolution_time_reversal
        (fun t : ℝ => |K t|) (fun _ : ℝ => (1 : ℝ))
        x hx.1.le)
  have hNorm :
      |∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume| ≤
      (∫ s in Ioc (0 : ℝ) x, |K (x - s)| * |V s| ∂volume) := by
    have hn := norm_integral_le_integral_norm
      (f := fun s : ℝ => K (x - s) * V s)
      (μ := volume.restrict (Ioc (0 : ℝ) x))
    simpa only [Real.norm_eq_abs, abs_mul] using hn
  calc
    _ ≤ ∫ s in Ioc (0 : ℝ) x, |K (x - s)| * |V s| ∂volume := hNorm
    _ ≤ sSup ((fun s : ℝ => |V s|) '' Ioc (0 : ℝ) R) *
      (∫ s in Ioc (0 : ℝ) x, |K (x - s)| ∂volume) := hp
    _ = _ := by rw [hRev]
