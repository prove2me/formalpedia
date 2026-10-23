-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_l1_continuous_solution_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:02:11.587548+00:00
-- url     : https://prove2.me/submissions/0057737a-dc57-43c1-b143-b243d96b5559

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_volterra_difference_homogeneous_of_solutions
import Theorems.Thm_AvramDividend_Classical_causal_volterra_exponential_kernel_weight_small
import Theorems.Thm_AvramDividend_Classical_causal_exponential_weighted_kernel_integrable
import Theorems.Thm_AvramDividend_Classical_positive_weighted_full_kernel_norm_small
import Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_bddAbove_of_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_homogeneous_weighted_sup_inequality
import Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_contraction_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (V G : ℝ → ℝ)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hGc : ContinuousOn G (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hGb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C)
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x)
    (hGe : ∀ x : ℝ, 0 < x →
      a * G x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * G s ∂volume) = x) :
    ∀ x : ℝ, 0 < x → V x = G x := by
  let D : ℝ → ℝ := fun x => V x - G x
  have hDc : ContinuousOn D (Ioi (0 : ℝ)) := hVc.sub hGc
  have hDb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |D x| ≤ C := by
    intro R hR
    obtain ⟨CV, hCV⟩ := hVb R hR
    obtain ⟨CG, hCG⟩ := hGb R hR
    refine ⟨CV + CG, ?_⟩
    intro x hx
    calc
      |D x| = |V x - G x| := rfl
      _ ≤ |V x| + |G x| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (V x) (0 : ℝ) (G x))
      _ ≤ CV + CG := add_le_add (hCV x hx) (hCG x hx)
  have hDeq : ∀ x : ℝ, 0 < x →
      a * D x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * D s ∂volume) = 0 := by
    exact causal_volterra_difference_homogeneous_of_solutions
      K V G a β hK hVc hGc hVb hGb hVe hGe
  obtain ⟨w, hw, hsmall⟩ :=
    causal_volterra_exponential_kernel_weight_small K a β ha hK
  have hKi :=
    causal_exponential_weighted_kernel_integrable K w hw.le hK
  obtain ⟨hLi, hLsmall⟩ :=
    positive_weighted_full_kernel_norm_small K a β w hw hKi hsmall
  let c : ℝ :=
    (∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume) / a
  have hc : c < 1 := by
    dsimp [c]
    exact (div_lt_one ha).2 hLsmall
  have hbound := causal_weighted_sup_bddAbove_of_locally_bounded
    D w hw.le hDb
  have hcontraction :
      ∀ R : ℝ, 0 < R → ∀ x ∈ Ioc (0 : ℝ) R,
        Real.exp (-(w * x)) * |D x| ≤
          c * sSup ((fun t : ℝ =>
            Real.exp (-(w * t)) * |D t|) '' Ioc (0 : ℝ) R) := by
    exact causal_homogeneous_weighted_sup_inequality
      K D a β w ha hw hK hDc hDb hDeq hsmall
  have hDzero := causal_weighted_sup_contraction_zero
    D w c hc hbound hcontraction
  intro x hx
  exact sub_eq_zero.mp (hDzero x hx)
