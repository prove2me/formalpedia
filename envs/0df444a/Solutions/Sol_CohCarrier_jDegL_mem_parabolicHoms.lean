-- Prove2me | solution 1 for CohCarrier.jDegL_mem_parabolicHoms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fcd783b0-fc42-5b8d-b3bc-71ff366a5dd1

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDegL_mem_parabolicHoms

set_option autoImplicit false

open Matrix CongruenceSubgroup
open scoped MatrixGroups

namespace CohCarrier
p2m_export "CohCarrier" "coresAdd GammaH H1 conjLowerMat LevelLE iotaDeg iotaDeg_injective pushChar jDegL"
namespace CorestrictionParabolic
p2m_open "CohCarrier"

private theorem fin_two_sq_eq_trace_smul_sub_one (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det = 1) :
    A ^ 2 = A.trace • A - 1 := by
  have hadj : A.adjugate = A.trace • 1 - A := by
    ext i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [Matrix.trace_fin_two, Matrix.one_fin_two]
  have hAA : A * A.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  rw [hadj, mul_sub, Matrix.mul_smul, mul_one, ← sq] at hAA
  have hrearr := sub_sub_cancel (A.trace • A) (A ^ 2)
  rw [hAA] at hrearr
  exact hrearr.symm

private theorem trace_sq_pow_of_det_one (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det = 1) (htr : A.trace ^ 2 = 4)
    (n : ℕ) : (A ^ n).trace ^ 2 = 4 := by
  have hrec : ∀ k, (A ^ (k + 2)).trace = A.trace * (A ^ (k + 1)).trace - (A ^ k).trace := by
    intro k
    have hstep : A ^ (k + 2) = A.trace • A ^ (k + 1) - A ^ k := by
      rw [show k + 2 = 2 + k from Nat.add_comm k 2, pow_add, fin_two_sq_eq_trace_smul_sub_one A hdet, sub_mul,
        smul_mul_assoc, ← pow_succ', one_mul]
    rw [hstep, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  have hinv : ∀ k, ((A ^ k).trace = 2 ∧ (A ^ (k + 1)).trace = A.trace) ∨
      ((A ^ k).trace = A.trace ∧ (A ^ (k + 1)).trace = 2) := by
    intro k
    induction k with
    | zero =>
      refine Or.inl ⟨?_, by rw [zero_add, pow_one]⟩
      rw [pow_zero, Matrix.trace_one, Fintype.card_fin]
      rfl
    | succ m ih =>
      rcases ih with ⟨he, ho⟩ | ⟨he, ho⟩
      · exact Or.inr ⟨ho, by rw [hrec m, ho, he, ← sq, htr]; ring⟩
      · exact Or.inl ⟨ho, by rw [hrec m, ho, he]; ring⟩
  rcases hinv n with ⟨hn, _⟩ | ⟨hn, _⟩
  · rw [hn]
    norm_num
  · rw [hn]
    exact htr

private theorem trace_conj (g x : SL(2, ℤ)) :
    ((x⁻¹ * g * x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mul]

private theorem trace_iotaDeg (M M' d : ℕ) [NeZero d] (h : LevelLE M M' ⊤ ⊤ d) (δ : ↥(GammaH M' ⊤)) :
    ((iotaDeg M M' ⊤ ⊤ d h δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  show ((conjLowerMat d (δ : SL(2, ℤ)) (h.dvd_entry δ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = _
  simp [conjLowerMat, Matrix.trace_fin_two]

private theorem pushChar_eq_zero (M M' d : ℕ) [NeZero d] (A : Type*) [AddCommGroup A] (h : LevelLE M M' ⊤ ⊤ d)
    (y : H1 M' ⊤ A) (hy : ModularCurve.Period.IsParabolicHom (GammaH M' ⊤) y)
    (k : ↥(iotaDeg M M' ⊤ ⊤ d h).range)
    (hk : (((k : ↥(GammaH M ⊤)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    pushChar M M' ⊤ ⊤ d A h y (Additive.ofMul k) = 0 := by
  set δ : ↥(GammaH M' ⊤) :=
    ((iotaDeg M M' ⊤ ⊤ d h).ofInjective (iotaDeg_injective M M' ⊤ ⊤ d h)).symm k with hδ
  have hιδ : iotaDeg M M' ⊤ ⊤ d h δ = (k : ↥(GammaH M ⊤)) := MonoidHom.apply_ofInjective_symm _ k
  have htr : ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
    rw [← trace_iotaDeg M M' d h δ, hιδ]
    exact hk
  show y (Additive.ofMul δ) = 0
  exact hy δ htr

end CohCarrier.CorestrictionParabolic

open CohCarrier.CorestrictionParabolic in

theorem solution (M M' d : ℕ) [NeZero M'] [NeZero d]
    (A : Type*) [AddCommGroup A] (R : Type*) [Semiring R] [Module R A]
    (h : CohCarrier.LevelLE M M' ⊤ ⊤ d) (y : CohCarrier.H1 M' ⊤ A)
    (hy : y ∈ ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M' ⊤) A) :
    CohCarrier.jDegL M M' ⊤ ⊤ d A R h y ∈ ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M ⊤) A := by
  show ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH M ⊤)
    (CohCarrier.coresAdd _ (CohCarrier.pushChar M M' ⊤ ⊤ d A h y))
  intro γ hγ
  classical
  letI : Fintype (↥(CohCarrier.GammaH M ⊤) ⧸ (CohCarrier.iotaDeg M M' ⊤ ⊤ d h).range) :=
    (CohCarrier.iotaDeg M M' ⊤ ⊤ d h).range.fintypeQuotientOfFiniteIndex
  simp only [CohCarrier.coresAdd, MonoidHom.toAdditiveLeft_apply_apply]
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  simp only [toAdd_prod, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  refine Finset.sum_eq_zero fun q _ => ?_
  refine pushChar_eq_zero M M' d A h y hy _ ?_
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, SubgroupClass.coe_pow]
  rw [trace_conj, Matrix.SpecialLinearGroup.coe_pow]
  exact trace_sq_pow_of_det_one _ (Matrix.SpecialLinearGroup.det_coe _) hγ _

end S_CohCarrier_jDegL_mem_parabolicHoms
end P2MW
export P2MW.S_CohCarrier_jDegL_mem_parabolicHoms (solution)
