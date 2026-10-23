-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_volterra_operator_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:04:04.132861+00:00
-- url     : https://prove2.me/submissions/1df32eb0-fe50-43ae-92fc-1f4e0812b613

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_locally_bounded_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_bddAbove_of_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_product_le_sup_mass
import Theorems.Thm_AvramDividend_Classical_causal_nonnegative_kernel_reflected_integral_le_global

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K V : ℝ → ℝ) (β w : ℝ) (hw : 0 ≤ w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C)
    (hLi : IntegrableOn (fun t : ℝ =>
      Real.exp (-w * t) * |β + K t|) (Ioi (0 : ℝ)) volume)
    (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R) :
    Real.exp (-(w * x)) *
      |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume| ≤
    sSup ((fun t : ℝ => Real.exp (-(w * t)) * |V t|) ''
      Ioc (0 : ℝ) R) *
    (∫ t in Ioi (0 : ℝ), Real.exp (-w * t) * |β + K t| ∂volume) := by
  let L : ℝ → ℝ := fun t => Real.exp (-w * t) * |β + K t|
  have hLn : ∀ t : ℝ, 0 ≤ L t := by
    intro t
    exact mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
  have hLb : IntegrableOn L (Ioi (0 : ℝ)) volume := hLi
  have hInt := causal_full_kernel_locally_bounded_input_integrable
    K V β hK hVc hVb x hx.1
  have hNorm :
      |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume| ≤
      ∫ s in Ioc (0 : ℝ) x, |(β + K (x - s)) * V s| ∂volume := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (f := fun s : ℝ => (β + K (x - s)) * V s)
        (μ := volume.restrict (Ioc (0 : ℝ) x)))
  have hPos : Real.exp (-(w * x)) *
      |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume| ≤
      ∫ s in Ioc (0 : ℝ) x,
        L (x - s) * (Real.exp (-(w * s)) * |V s|) ∂volume := by
    calc
      _ ≤ Real.exp (-(w * x)) *
        (∫ s in Ioc (0 : ℝ) x, |(β + K (x - s)) * V s| ∂volume) :=
        mul_le_mul_of_nonneg_left hNorm (Real.exp_nonneg _)
      _ = ∫ s in Ioc (0 : ℝ) x,
          Real.exp (-(w * x)) * |(β + K (x - s)) * V s| ∂volume := by
        rw [integral_const_mul]
      _ = ∫ s in Ioc (0 : ℝ) x,
          L (x - s) * (Real.exp (-(w * s)) * |V s|) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with s
        have hexp : -(w * x) = -(w * (x - s)) + -(w * s) := by ring
        rw [abs_mul, hexp, Real.exp_add]
        dsimp [L]
        rw [← neg_mul]
        ring
  have hMb := causal_weighted_sup_bddAbove_of_locally_bounded
    V w hw hVb R hR
  let M : ℝ := sSup ((fun t : ℝ =>
    Real.exp (-(w * t)) * |V t|) '' Ioc (0 : ℝ) R)
  have hMn : 0 ≤ M := by
    calc
      0 ≤ Real.exp (-(w * x)) * |V x| :=
        mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
      _ ≤ M := le_csSup hMb ⟨x, hx, rfl⟩
  have hp := causal_weighted_kernel_product_le_sup_mass
    L V w R x hLb hLn hVc hR hx hMb
  have hm := causal_nonnegative_kernel_reflected_integral_le_global
    L hLb (fun t ht => hLn t) x hx.1
  change Real.exp (-(w * x)) *
      |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume| ≤
      M * (∫ t in Ioi (0 : ℝ), L t ∂volume)
  calc
    _ ≤ ∫ s in Ioc (0 : ℝ) x,
      L (x - s) * (Real.exp (-(w * s)) * |V s|) ∂volume := hPos
    _ ≤ M * (∫ s in Ioc (0 : ℝ) x, L (x - s) ∂volume) := hp
    _ ≤ M * (∫ t in Ioi (0 : ℝ), L t ∂volume) :=
      mul_le_mul_of_nonneg_left hm hMn
