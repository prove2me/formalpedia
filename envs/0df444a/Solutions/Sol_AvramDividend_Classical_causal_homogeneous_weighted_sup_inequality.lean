-- Prove2me | solution 1 for AvramDividend.Classical.causal_homogeneous_weighted_sup_inequality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:57:43.8534+00:00
-- url     : https://prove2.me/submissions/ef1a87d9-0e9c-4013-ab0d-661cc2a84442

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_exponential_weighted_kernel_integrable
import Theorems.Thm_AvramDividend_Classical_positive_weighted_full_kernel_norm_small
import Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_bddAbove_of_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_homogeneous_weighted_integral_bound
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_product_le_sup_mass
import Theorems.Thm_AvramDividend_Classical_causal_nonnegative_kernel_reflected_integral_le_global

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K D : ℝ → ℝ) (a β w : ℝ)
    (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hDc : ContinuousOn D (Ioi (0 : ℝ)))
    (hDb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ t : ℝ, t ∈ Ioc (0 : ℝ) R → |D t| ≤ C)
    (hEq : ∀ x : ℝ, 0 < x →
      a * D x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * D s ∂volume) = 0)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ),
        |K t| * Real.exp (-w * t) ∂volume) < a) :
    ∀ R : ℝ, 0 < R → ∀ x ∈ Ioc (0 : ℝ) R,
      Real.exp (-(w * x)) * |D x| ≤
        ((∫ t in Ioi (0 : ℝ),
          Real.exp (-w * t) * |β + K t| ∂volume) / a) *
        sSup ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
          Ioc (0 : ℝ) R) := by
  let L : ℝ → ℝ := fun t => Real.exp (-w * t) * |β + K t|
  have hKi := causal_exponential_weighted_kernel_integrable K w hw.le hK
  obtain ⟨hLi, hLsmall⟩ :=
    positive_weighted_full_kernel_norm_small K a β w hw hKi hsmall
  change IntegrableOn L (Ioi (0 : ℝ)) volume at hLi
  have hLn : ∀ t : ℝ, 0 ≤ L t := by
    intro t
    exact mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
  intro R hR x hx
  have hxpos : 0 < x := hx.1
  let M : ℝ := sSup ((fun t : ℝ =>
    Real.exp (-(w * t)) * |D t|) '' Ioc (0 : ℝ) R)
  have hMb : BddAbove ((fun t : ℝ =>
      Real.exp (-(w * t)) * |D t|) '' Ioc (0 : ℝ) R) :=
    causal_weighted_sup_bddAbove_of_locally_bounded D w hw.le hDb R hR
  have hMn : 0 ≤ M := by
    calc
      0 ≤ Real.exp (-(w * x)) * |D x| :=
        mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
      _ ≤ M := le_csSup hMb ⟨x, hx, rfl⟩
  have hp := causal_homogeneous_weighted_integral_bound
    K D a β w ha hK hDc hDb hEq x hxpos
  have hm := causal_weighted_kernel_product_le_sup_mass
    L D w R x hLi hLn hDc hR hx hMb
  have hg := causal_nonnegative_kernel_reflected_integral_le_global
    L hLi (fun t ht => hLn t) x hxpos
  have hle : a * (Real.exp (-(w * x)) * |D x|) ≤
      M * (∫ t in Ioi (0 : ℝ), L t ∂volume) := by
    calc
      _ ≤ ∫ s in Ioc (0 : ℝ) x,
        L (x - s) * (Real.exp (-(w * s)) * |D s|) ∂volume := by
          simpa only [L, neg_mul] using hp
      _ ≤ M * (∫ s in Ioc (0 : ℝ) x, L (x - s) ∂volume) := hm
      _ ≤ M * (∫ t in Ioi (0 : ℝ), L t ∂volume) :=
        mul_le_mul_of_nonneg_left hg hMn
  have hf : Real.exp (-(w * x)) * |D x| ≤
      (M * (∫ t in Ioi (0 : ℝ), L t ∂volume)) / a := by
    apply (le_div_iff₀ ha).2
    nlinarith [hle]
  change Real.exp (-(w * x)) * |D x| ≤
    ((∫ t in Ioi (0 : ℝ), L t ∂volume) / a) * M
  calc
    _ ≤ (M * (∫ t in Ioi (0 : ℝ), L t ∂volume)) / a := hf
    _ = _ := by ring
