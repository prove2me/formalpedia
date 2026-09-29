-- Prove2me | solution 1 for CohCarrier.index_GammaHUpper_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/669039b3-d3e3-513b-b3fe-8e42003a3e7f

import Definitions.Def_CohCarrier_Level
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_index_GammaHUpper_of_prime

set_option autoImplicit false

namespace IharaSolIdx

open CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem mul_inv_apply_01 (x y : SL(2, ℤ)) : (x * y⁻¹) 0 1 = -(x 0 0 * y 0 1) + x 0 1 * y 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def uMat (t : ℤ) : SL(2, ℤ) :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem uMat_00 (t : ℤ) : (uMat t) 0 0 = 1 := rfl
@[scoped simp] theorem uMat_01 (t : ℤ) : (uMat t) 0 1 = t := rfl
@[scoped simp] theorem uMat_10 (t : ℤ) : (uMat t) 1 0 = 0 := rfl
@[scoped simp] theorem uMat_11 (t : ℤ) : (uMat t) 1 1 = 1 := rfl

def gInf (b : ℤ) (M : ℕ) : SL(2, ℤ) :=
  ⟨!![1 + b * M, b; M, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem gInf_00 (b : ℤ) (M : ℕ) : (gInf b M) 0 0 = 1 + b * M := rfl
@[scoped simp] theorem gInf_01 (b : ℤ) (M : ℕ) : (gInf b M) 0 1 = b := rfl
@[scoped simp] theorem gInf_10 (b : ℤ) (M : ℕ) : (gInf b M) 1 0 = M := rfl
@[scoped simp] theorem gInf_11 (b : ℤ) (M : ℕ) : (gInf b M) 1 1 = 1 := rfl

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

theorem uMat_mem (t : ℤ) : uMat t ∈ CohCarrier.GammaH M H := by
  have h0 : uMat t ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show ((0 : ℤ) : ZMod M) = 0
    exact Int.cast_zero
  refine CohCarrier.mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : CohCarrier.gamma0Units M ⟨uMat t, h0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    show ((1 : ℤ) : ZMod M) = 1
    exact Int.cast_one
  rw [e]
  exact H.one_mem

theorem gInf_mem (b : ℤ) : gInf b M ∈ CohCarrier.GammaH M H := by
  have h0 : gInf b M ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show (((M : ℕ) : ℤ) : ZMod M) = 0
    rw [Int.cast_natCast, ZMod.natCast_self]
  refine CohCarrier.mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : CohCarrier.gamma0Units M ⟨gInf b M, h0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    show ((1 : ℤ) : ZMod M) = 1
    exact Int.cast_one
  rw [e]
  exact H.one_mem

def uElt (t : ℤ) : ↥(CohCarrier.GammaH M H) := ⟨uMat t, uMat_mem M H t⟩

def gElt (b : ℤ) : ↥(CohCarrier.GammaH M H) := ⟨gInf b M, gInf_mem M H b⟩

@[scoped simp] theorem uElt_coe (t : ℤ) : ((uElt M H t : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) = uMat t := rfl
@[scoped simp] theorem gElt_coe (b : ℤ) : ((gElt M H b : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) = gInf b M := rfl

theorem mk_eq_mk_iff (x y : ↥(CohCarrier.GammaH M H)) :
    (Quotient.mk'' x : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = Quotient.mk'' y ↔
      ((((y : SL(2, ℤ)) * (x : SL(2, ℤ))⁻¹) 0 1 : ℤ) : ZMod ℓ) = 0 := by
  rw [Quotient.eq'', QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper, Subgroup.coe_mul,
    Subgroup.coe_inv]

theorem natCard_rightQuot_GammaHUpper [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    Nat.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = ℓ + 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨u, v, huv⟩ : IsCoprime (ℓ : ℤ) (M : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)
  have Hl : ((ℓ : ℕ) : ZMod ℓ) = 0 := ZMod.natCast_self ℓ
  have H1 := congrArg (Int.cast : ℤ → ZMod ℓ) huv
  push_cast at H1

  have H0 : (1 : ZMod ℓ) + -(v : ZMod ℓ) * (M : ZMod ℓ) = 0 := by linear_combination -H1 + (u : ZMod ℓ) * Hl
  have H2 : (v : ZMod ℓ) * (M : ZMod ℓ) = 1 := by linear_combination H1 - (u : ZMod ℓ) * Hl

  have hNU : ∀ j : ZMod ℓ,
      (Quotient.mk'' (gElt M H (-v)) : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) =
        Quotient.mk'' (uElt M H (j.val : ℤ)) → False := by
    intro j h
    rw [mk_eq_mk_iff, mul_inv_apply_01] at h
    simp only [uElt_coe, gElt_coe, uMat_00, uMat_01, gInf_00, gInf_01] at h
    push_cast at h
    simp only [ZMod.natCast_zmod_val] at h

    have H3 : (v : ZMod ℓ) = 0 := by linear_combination h - j * H0
    have H4 : (0 : ZMod ℓ) = 1 := by linear_combination H2 - (M : ZMod ℓ) * H3
    exact zero_ne_one H4

  have hUU : ∀ j j' : ZMod ℓ,
      (Quotient.mk'' (uElt M H (j.val : ℤ)) : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) =
        Quotient.mk'' (uElt M H (j'.val : ℤ)) → j = j' := by
    intro j j' h
    rw [mk_eq_mk_iff, mul_inv_apply_01] at h
    simp only [uElt_coe, uMat_00, uMat_01] at h
    push_cast at h
    simp only [ZMod.natCast_zmod_val] at h

    linear_combination -h
  let ψ : Option (ZMod ℓ) → Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ)) :=
    fun o => o.elim (Quotient.mk'' (gElt M H (-v))) fun j => Quotient.mk'' (uElt M H (j.val : ℤ))
  have hinj : Function.Injective ψ := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some j => exact (hNU j hxy).elim
    | some j =>
      cases y with
      | none => exact (hNU j hxy.symm).elim
      | some j' => exact congrArg some (hUU j j' hxy)
  have hsurj : Function.Surjective ψ := by
    intro q
    induction q using Quotient.inductionOn' with
    | h g =>
      by_cases ha : (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ) = 0
      · refine ⟨none, ?_⟩
        show (Quotient.mk'' (gElt M H (-v)) : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) =
          Quotient.mk'' g
        rw [mk_eq_mk_iff, mul_inv_apply_01]
        simp only [gElt_coe, gInf_00, gInf_01]
        push_cast
        linear_combination (v : ZMod ℓ) * ha + ((((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ)) * H0
      · obtain ⟨j, hj⟩ : ∃ j : ZMod ℓ, (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ) * j = (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) :=
          ⟨((((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ))⁻¹ * (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ), by
            rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]⟩
        refine ⟨some j, ?_⟩
        show (Quotient.mk'' (uElt M H (j.val : ℤ)) : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) =
          Quotient.mk'' g
        rw [mk_eq_mk_iff, mul_inv_apply_01]
        simp only [uElt_coe, uMat_00, uMat_01]
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination -hj
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]

theorem index_GammaHUpper_prime [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    (CohCarrier.GammaHUpper M H ℓ).index = ℓ + 1 := by
  rw [Subgroup.index, ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (CohCarrier.GammaHUpper M H ℓ))]
  exact natCard_rightQuot_GammaHUpper M H ℓ hℓ hℓM

theorem card_rightQuot_GammaHUpper [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    Fintype.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = ℓ + 1 := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_rightQuot_GammaHUpper M H ℓ hℓ hℓM

end IharaSolIdx
p2m_reactivate "P2MW.S_CohCarrier_index_GammaHUpper_of_prime.IharaSolIdx"

open CohCarrier in
theorem solution (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    (GammaHUpper M H ℓ).index = ℓ + 1 :=
  IharaSolIdx.index_GammaHUpper_prime M H ℓ hℓ hℓM

#print axioms solution

end S_CohCarrier_index_GammaHUpper_of_prime
end P2MW
export P2MW.S_CohCarrier_index_GammaHUpper_of_prime (solution)
