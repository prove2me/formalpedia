-- Prove2me | solution 1 for Finsupp.forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1a6415a1-e537-5140-bfc7-49c1a4da6c18

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Finsupp_forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq

set_option autoImplicit false

p2m_open "Polynomial CuspidalType P2MW.S_Finsupp_forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq.CuspidalType"

open Finset

namespace CuspidalType
namespace NV3Arch
namespace C7b
p2m_open "CuspidalType"

theorem sum_coe_apply_mul_coe_apply_inv {C : Type*} [CommGroup C] [Fintype C] {K : Type*} [Field K]
    [DecidableEq (C →* Kˣ)] (μ ν : C →* Kˣ) :
    ∑ c, ((μ c : Kˣ) : K) * ((ν c⁻¹ : Kˣ) : K) = if μ = ν then (Fintype.card C : K) else 0 := by
  classical
  have key : ∀ c, ((μ c : Kˣ) : K) * ((ν c⁻¹ : Kˣ) : K) = ((Units.coeHom K).comp (μ * ν⁻¹)) c := by
    intro c
    simp [map_inv]
  simp_rw [key]
  rw [sum_hom_units]
  have hiff : (Units.coeHom K).comp (μ * ν⁻¹) = 1 ↔ μ = ν := by
    constructor
    · intro h
      rw [← mul_inv_eq_one]
      refine MonoidHom.ext fun c => ?_
      have hc := DFunLike.congr_fun h c
      simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply, MonoidHom.one_apply] at hc
      rw [MonoidHom.one_apply]
      exact Units.val_eq_one.1 hc
    · rintro rfl
      exact MonoidHom.ext fun c => by simp
  by_cases h : μ = ν
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (mt hiff.1 h), if_neg h, Nat.cast_zero]

end CuspidalType.NV3Arch.C7b

open CuspidalType.NV3Arch.C7b in

theorem solution {C : Type*} [CommGroup C] [Fintype C] {K : Type*} [Field K] [CharZero K]
    (m : (C →* Kˣ) →₀ ℕ) (f : C → K) (hf : ∀ c, f c = m.sum fun μ n => (n : K) * ((μ c : Kˣ) : K))
    (h1 : ∑ c, f c = Fintype.card C)
    (h2 : ∑ c, f c * f c⁻¹ = (m.sum fun _ n => (n : K)) * Fintype.card C) :
    (∀ μ, m μ ≤ 1) ∧ m 1 = 1 := by
  classical
  have hC : (Fintype.card C : K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  set s := m.support with hs
  have hf' : ∀ c, f c = ∑ μ ∈ s, (m μ : K) * ((μ c : Kˣ) : K) := hf

  have e1 : ∑ c, f c = (m 1 : K) * Fintype.card C := by
    simp_rw [hf']
    rw [sum_comm]
    simp_rw [← mul_sum]
    have h1' : ∀ μ : C →* Kˣ, ∑ c, ((μ c : Kˣ) : K) = if μ = 1 then (Fintype.card C : K) else 0 := by
      intro μ
      simpa using sum_coe_apply_mul_coe_apply_inv μ 1
    simp_rw [h1', mul_ite, mul_zero]
    rw [sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [Finsupp.notMem_support_iff.1 h, Nat.cast_zero, zero_mul]
  have hm1 : m 1 = 1 := by
    have : (m 1 : K) * Fintype.card C = 1 * Fintype.card C := by rw [← e1, h1, one_mul]
    exact_mod_cast mul_right_cancel₀ hC this

  have e2 : ∑ c, f c * f c⁻¹ = (∑ μ ∈ s, ((m μ : K)) ^ 2) * Fintype.card C := by
    calc ∑ c, f c * f c⁻¹
        = ∑ c, ∑ μ ∈ s, ∑ ν ∈ s, ((m μ : K) * (m ν : K)) * (((μ c : Kˣ) : K) * ((ν c⁻¹ : Kˣ) : K)) := by
          refine sum_congr rfl fun c _ => ?_
          rw [hf' c, hf' c⁻¹, sum_mul_sum]
          refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => ?_
          ring
      _ = ∑ μ ∈ s, ∑ ν ∈ s, ((m μ : K) * (m ν : K)) * ∑ c, (((μ c : Kˣ) : K) * ((ν c⁻¹ : Kˣ) : K)) := by
          rw [sum_comm]
          refine sum_congr rfl fun μ _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun ν _ => ?_
          rw [mul_sum]
      _ = ∑ μ ∈ s, ((m μ : K) * (m μ : K)) * Fintype.card C := by
          refine sum_congr rfl fun μ hμ => ?_
          simp_rw [sum_coe_apply_mul_coe_apply_inv, mul_ite, mul_zero]
          rw [sum_ite_eq]
          rw [if_pos hμ]
      _ = (∑ μ ∈ s, ((m μ : K)) ^ 2) * Fintype.card C := by
          rw [sum_mul]
          refine sum_congr rfl fun μ _ => ?_
          ring
  have hsq : ∑ μ ∈ s, (m μ) ^ 2 = ∑ μ ∈ s, m μ := by
    have : (∑ μ ∈ s, ((m μ : K)) ^ 2) * Fintype.card C = (∑ μ ∈ s, (m μ : K)) * Fintype.card C := by
      rw [← e2, h2]; rfl
    have := mul_right_cancel₀ hC this
    exact_mod_cast this
  have hle : ∀ μ ∈ s, m μ ≤ (m μ) ^ 2 := fun μ _ => Nat.le_self_pow two_ne_zero _
  have heq := (sum_eq_sum_iff_of_le hle).1 hsq.symm
  refine ⟨fun μ => ?_, hm1⟩
  by_cases hμ : μ ∈ s
  · have h := heq μ hμ
    rcases Nat.eq_zero_or_pos (m μ) with h0 | hpos
    · omega
    · have : m μ * 1 = m μ * m μ := by rw [mul_one, ← sq]; exact h
      have := Nat.eq_of_mul_eq_mul_left hpos this
      omega
  · rw [Finsupp.notMem_support_iff.1 hμ]; exact zero_le_one

end S_Finsupp_forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq
end P2MW
export P2MW.S_Finsupp_forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq (solution)
