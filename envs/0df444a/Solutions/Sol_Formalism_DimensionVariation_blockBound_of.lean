-- Prove2me | solution 1 for Formalism.DimensionVariation.blockBound_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:48.149076+00:00
-- url     : https://prove2.me/submissions/839e4f24-db4d-4949-b981-7dc4abebaaf8

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf

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
theorem _root_.solution (hF : FockJet) (hI : BlockIntegral) : BlockBound := by
  intro Pl ι _ _ W _ _ _ r ν n s Th c Rc lam Om S hν hνn hs hsq hTc hTs hTb hsupp hR hOm hlam
  have hB := hI Pl ι W r ν s Th (fun u => Rc.sum (fun e A => mono (cj u) e • A)) S hν hs hsq hTb hR
  have hJ := hF (Pl × ι) Th c S hTc hTs hTb
  have h1 : ∀ e (u : Pl × ι → ℂ), (Th u * (Real.exp (-(nsq u)) : ℂ)) • mono (cj u) e • Rc e =
      (Th u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) • Rc e := fun e u => by
    rw [smul_smul]; congr 1; ring
  have hint : ∫ u : Pl × ι → ℂ, (Th u * (Real.exp (-(nsq u)) : ℂ)) • Rc.sum (fun e A => mono (cj u) e • A) =
      (π : ℂ) ^ (Fintype.card Pl * Fintype.card ι) • Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A) := by
    simp only [Finsupp.sum, Finset.smul_sum]
    simp_rw [h1]
    rw [integral_finset_sum _ fun e _ => (hJ e).1.smul_const (Rc e)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [integral_smul_const, (hJ e).2, Fintype.card_prod, smul_smul]
  have hP : Rc.sum (fun e A => (c e * (mfact e : ℂ) * ∏ x : Pl × ι, lam x.1 ^ e x) • A) =
      (∏ τ, lam τ ^ n τ) • Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A) := by
    simp only [Finsupp.sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hl : ∏ x : Pl × ι, lam x.1 ^ e x = ∏ τ, lam τ ^ n τ := by
      simp only [Fintype.prod_prod_type, Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun τ _ => by rw [hsupp e he τ]
    rw [hl, smul_smul, mul_comm (∏ τ, lam τ ^ n τ)]
  set X := Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A) with hXdef
  have hpi : (0 : ℝ) < π ^ (Fintype.card Pl * Fintype.card ι) := by positivity
  have hX : ‖X‖ ≤ S * ∏ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι *
      Real.exp ((∑ i, ph (ν τ i)) / 2)) := by
    rw [hint, norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      mul_div_cancel_left₀ _ hpi.ne'] at hB
    simpa only [hνn] using hB
  have e1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have e2 : ∀ x : ℝ, Real.exp (x / 2) ^ 2 = Real.exp x := fun x => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hY : ∀ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι *
      Real.exp ((∑ i, ph (ν τ i)) / 2)) ^ 2 = Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) *
      Real.exp (∑ i, ph (ν τ i)) := fun τ => by
    rw [mul_pow, mul_pow, e1, e2, ← pow_mul, mul_comm (Fintype.card ι) 2]
  have hS : ‖X‖ ^ 2 ≤ S ^ 2 * ∏ τ, (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) *
      Real.exp (∑ i, ph (ν τ i))) := by
    have h2 : ‖X‖ ^ 2 ≤ (S * ∏ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι *
        Real.exp ((∑ i, ph (ν τ i)) / 2))) ^ 2 := by gcongr
    rwa [mul_pow, ← Finset.prod_pow, Finset.prod_congr rfl fun τ _ => hY τ] at h2
  have hL : ‖∏ τ, lam τ ^ n τ‖ ^ 2 = ∏ τ, (Om τ)⁻¹ ^ n τ := by
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_pow, ← pow_mul, mul_comm, pow_mul, hlam]
  rw [hP, norm_smul, mul_pow, hL, Finset.prod_mul_distrib, mul_left_comm (S ^ 2)]
  exact mul_le_mul_of_nonneg_left hS
    (Finset.prod_nonneg fun τ _ => pow_nonneg (inv_nonneg.2 (hOm τ).le) _)
end Formalism.DimensionVariation
