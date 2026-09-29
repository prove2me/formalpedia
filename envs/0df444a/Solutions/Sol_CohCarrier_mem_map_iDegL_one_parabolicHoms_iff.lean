-- Prove2me | solution 1 for CohCarrier.mem_map_iDegL_one_parabolicHoms_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1cbd00c3-7786-5876-b182-859c96498f4a

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_mem_map_iDegL_one_parabolicHoms_iff
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq"

set_option autoImplicit false

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace CohL2
namespace WChar

theorem fin_two_sq_eq_trace_smul_sub_one (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det = 1) :
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

theorem trace_sq_pow_of_det_one (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det = 1)
    (htr : A.trace ^ 2 = 4) (n : ℕ) : (A ^ n).trace ^ 2 = 4 := by
  have hrec : ∀ k, (A ^ (k + 2)).trace = A.trace * (A ^ (k + 1)).trace - (A ^ k).trace := by
    intro k
    have hstep : A ^ (k + 2) = A.trace • A ^ (k + 1) - A ^ k := by
      rw [show k + 2 = 2 + k from Nat.add_comm k 2, pow_add, fin_two_sq_eq_trace_smul_sub_one A hdet,
        sub_mul, smul_mul_assoc, ← pow_succ', one_mul]
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
  · rw [hn]; norm_num
  · rw [hn]; exact htr

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem conjLowerMat_one (A : SL(2, ℤ)) (h : ((1 : ℕ) : ℤ) ∣ A 1 0) :
    CohCarrier.conjLowerMat 1 A h = A := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [CohCarrier.conjLowerMat]

theorem coe_iotaDeg_one (h : CohCarrier.LevelLE M M ⊤ H 1) (γ : ↥(CohCarrier.GammaH M H)) :
    ((CohCarrier.iotaDeg M M ⊤ H 1 h γ : ↥(CohCarrier.GammaH M ⊤)) : SL(2, ℤ)) = γ :=
  conjLowerMat_one (γ : SL(2, ℤ)) (h.dvd_entry γ)

theorem pow_index_mem_GammaH (u : ↥(CohCarrier.GammaH M ⊤)) :
    (u : SL(2, ℤ)) ^ H.index ∈ CohCarrier.GammaH M H := by
  obtain ⟨hu0, _⟩ := CohCarrier.mem_GammaH_iff.mp u.2
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨Subgroup.pow_mem _ hu0 _, ?_⟩
  have : (⟨(u : SL(2, ℤ)) ^ H.index, Subgroup.pow_mem _ hu0 _⟩ : Gamma0 M) =
      (⟨(u : SL(2, ℤ)), hu0⟩ : Gamma0 M) ^ H.index := Subtype.ext (by simp)
  rw [this, map_pow]
  exact Subgroup.pow_index_mem H _

end CohL2.WChar

open CohL2.WChar in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
    (h₁ : CohCarrier.LevelLE M M ⊤ H 1) (hunit : IsUnit ((H.index : ℕ) : R)) (φ : CohCarrier.H1 M H A) :
    φ ∈ (ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M ⊤) A).map
        (CohCarrier.iDegL M M ⊤ H 1 A R h₁) ↔
      (φ ∈ ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) A ∧
        ∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ) := by
  obtain ⟨_, _, hrange, _⟩ :=
    CohCarrier.injective_iDeg_one_and_range_eq_of_isUnit_index M H R A h₁ hunit
  constructor
  · rintro ⟨x₀, hx₀, rfl⟩
    refine ⟨?_, ?_⟩
    ·
      intro γ hγ
      show x₀ (Additive.ofMul (CohCarrier.iotaDeg M M ⊤ H 1 h₁ γ)) = 0
      apply hx₀
      rw [coe_iotaDeg_one M H h₁ γ]
      exact hγ
    ·
      have hmem : (CohCarrier.iDegL M M ⊤ H 1 A R h₁ x₀ : CohCarrier.H1 M H A) ∈
          Set.range (CohCarrier.iDeg' M M ⊤ H 1 A h₁) := ⟨x₀, rfl⟩
      rw [hrange] at hmem
      exact hmem
  · rintro ⟨hpar, hinv⟩
    have hmem : φ ∈ Set.range (CohCarrier.iDeg' M M ⊤ H 1 A h₁) := by rw [hrange]; exact hinv
    obtain ⟨x₀, rfl⟩ := hmem
    refine ⟨x₀, ?_, rfl⟩

    intro u hu
    set n := H.index with hn
    let γ : ↥(CohCarrier.GammaH M H) := ⟨(u : SL(2, ℤ)) ^ n, pow_index_mem_GammaH M H u⟩
    have hγtr : (((γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
      show ((((u : SL(2, ℤ)) ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace ^ 2 = 4
      rw [Matrix.SpecialLinearGroup.coe_pow]
      exact trace_sq_pow_of_det_one _ (Matrix.SpecialLinearGroup.det_coe _) hu n
    have h0 : (CohCarrier.iDeg' M M ⊤ H 1 A h₁ x₀) (Additive.ofMul γ) = 0 := hpar γ hγtr
    have hι : CohCarrier.iotaDeg M M ⊤ H 1 h₁ γ = u ^ n := by
      apply Subtype.ext
      rw [coe_iotaDeg_one M H h₁ γ]
      simp [γ]
    have h1 : (CohCarrier.iDeg' M M ⊤ H 1 A h₁ x₀) (Additive.ofMul γ) = n • x₀ (Additive.ofMul u) := by
      show x₀ (Additive.ofMul (CohCarrier.iotaDeg M M ⊤ H 1 h₁ γ)) = _
      rw [hι, ofMul_pow, map_nsmul]
    rw [h1, ← Nat.cast_smul_eq_nsmul R] at h0
    have : ((n : ℕ) : R) • x₀ (Additive.ofMul u) = ((n : ℕ) : R) • (0 : A) := by rw [h0, smul_zero]
    exact (hunit.smul_left_cancel).mp this

end S_CohCarrier_mem_map_iDegL_one_parabolicHoms_iff
end P2MW
export P2MW.S_CohCarrier_mem_map_iDegL_one_parabolicHoms_iff (solution)
