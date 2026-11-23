-- Prove2me | solution 1 for Formalism.DimensionVariation.blockIntegral_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:58.553802+00:00
-- url     : https://prove2.me/submissions/5f888a89-57a5-46a0-9667-9a5eb22acaad

import Mathlib
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialSandwich
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf
import Theorems.Thm_Formalism_DimensionVariation_placeBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory
open scoped ComplexConjugate Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution (hG : GaussCoord) : BlockIntegral := by
  intro Pl ι _ _ W _ _ r ν s Th R S hν hs hsq hTh hR
  have hS : 0 ≤ S := by
    by_contra hneg
    push_neg at hneg
    have h0 := (norm_nonneg _).trans (hTh 0)
    have := mul_neg_of_neg_of_pos hneg (Real.exp_pos (nsq (0 : Pl × ι → ℂ) / 2))
    linarith
  have hN1 : ∀ τ, 0 < (∑ i, ν τ i) + 1 := fun τ => by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hν τ i
    linarith
  have hbpos : ∀ x : Pl × ι, 0 < 1 / ((∑ i, ν x.1 i) + 1) / 2 := fun x =>
    div_pos (div_pos one_pos (hN1 x.1)) two_pos
  have hGb := hG (Pl × ι) (fun x => 1 / ((∑ i, ν x.1 i) + 1) / 2) hbpos
  set C := ∏ τ, (Real.exp (1 / 2) * Real.exp ((∑ i, ph (ν τ i)) / 2)) with hC
  have hpt : ∀ u : Pl × ι → ℂ, ‖(Th u * (Real.exp (-(nsq u)) : ℂ)) • R u‖ ≤
      S * C * Real.exp (-∑ x : Pl × ι, 1 / ((∑ i, ν x.1 i) + 1) / 2 * ‖u x‖ ^ 2) := by
    intro u
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hsplitN : nsq u = ∑ τ, nsq (fun x => u (τ, x)) := by
      simp only [nsq]; rw [Fintype.sum_prod_type]
    have hplace : ∀ τ, (∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) * Real.exp (-(nsq fun x => u (τ, x)) / 2) ≤
        Real.exp (1 / 2) * Real.exp ((∑ i, ph (ν τ i)) / 2) *
          Real.exp (-(1 / ((∑ i, ν τ i) + 1)) * (nsq fun x => u (τ, x)) / 2) :=
      fun τ => placeBound r (ν τ) (s τ _) _ (hν τ) (hs τ _) (hsq τ _)
    have hexp : Real.exp (-∑ x : Pl × ι, 1 / ((∑ i, ν x.1 i) + 1) / 2 * ‖u x‖ ^ 2) =
        ∏ τ, Real.exp (-(1 / ((∑ i, ν τ i) + 1)) * (nsq fun x => u (τ, x)) / 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [nsq]
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have he : Real.exp (nsq u / 2) * Real.exp (-nsq u) = ∏ τ, Real.exp (-(nsq fun x => u (τ, x)) / 2) := by
      rw [← Real.exp_add, ← Real.exp_sum]
      congr 1
      rw [hsplitN, ← Finset.sum_neg_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => by ring
    calc ‖Th u‖ * Real.exp (-nsq u) * ‖R u‖
        ≤ S * Real.exp (nsq u / 2) * Real.exp (-nsq u) * ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hTh u) (Real.exp_pos _).le) (hR u) (norm_nonneg _)
            (mul_nonneg (mul_nonneg hS (Real.exp_pos _).le) (Real.exp_pos _).le)
      _ = S * ∏ τ, ((∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) * Real.exp (-(nsq fun x => u (τ, x)) / 2)) := by
          rw [Finset.prod_mul_distrib, ← he]; ring
      _ ≤ S * ∏ τ, (Real.exp (1 / 2) * Real.exp ((∑ i, ph (ν τ i)) / 2) *
            Real.exp (-(1 / ((∑ i, ν τ i) + 1)) * (nsq fun x => u (τ, x)) / 2)) :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun τ _ => mul_nonneg
            (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hs τ _ i) _) (Real.exp_pos _).le)
            fun τ _ => hplace τ) hS
      _ = _ := by rw [hexp, Finset.prod_mul_distrib, hC, mul_assoc]
  have hint := norm_integral_le_of_norm_le (hGb.1.const_mul (S * C)) (Filter.Eventually.of_forall hpt)
  have hprod : ∏ x : Pl × ι, π / (1 / ((∑ i, ν x.1 i) + 1) / 2) =
      π ^ (Fintype.card Pl * Fintype.card ι) * ∏ τ, (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι := by
    rw [Fintype.prod_prod_type]
    have hb : ∀ τ, ∏ i : ι, π / (1 / ((∑ j, ν (τ, i).1 j) + 1) / 2) =
        π ^ Fintype.card ι * (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι := fun τ => by
      have hne := (hN1 τ).ne'
      have hi : ∀ i : ι, π / (1 / ((∑ j, ν (τ, i).1 j) + 1) / 2) = π * (2 * (∑ i, ν τ i) + 2) :=
        fun i => by first | (field_simp; ring) | field_simp
      rw [Finset.prod_congr rfl fun i _ => hi i, Finset.prod_const, Finset.card_univ, mul_pow]
    rw [Finset.prod_congr rfl fun τ _ => hb τ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← pow_mul, mul_comm (Fintype.card ι)]
  rw [integral_const_mul, hGb.2, hprod] at hint
  have hpi : (0 : ℝ) < π ^ (Fintype.card Pl * Fintype.card ι) := by positivity
  rw [div_le_iff₀ hpi]
  calc _ ≤ _ := hint
    _ = _ := by
      have hr : ∀ τ, Real.exp (1 / 2) * (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι *
          Real.exp ((∑ i, ph (ν τ i)) / 2) = (Real.exp (1 / 2) * Real.exp ((∑ i, ph (ν τ i)) / 2)) *
          (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι := fun τ => by ring
      rw [Finset.prod_congr rfl fun τ _ => hr τ, Finset.prod_mul_distrib, ← hC]
      ring
end Formalism.DimensionVariation
