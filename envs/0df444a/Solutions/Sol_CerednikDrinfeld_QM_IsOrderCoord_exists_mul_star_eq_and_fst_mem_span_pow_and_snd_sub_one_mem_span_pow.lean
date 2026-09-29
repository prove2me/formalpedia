-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsOrderCoord.exists_mul_star_eq_and_fst_mem_span_pow_and_snd_sub_one_mem_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/3f258769-16df-5f20-b5a0-5e8efae516f5

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_IsOrder_star_mem_and_exists_int_trd_nrd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsOrderCoord_exists_mul_star_eq_and_fst_mem_span_pow_and_snd_sub_one_mem_span_pow

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld CerednikDrinfeld.QM

namespace E33W2

section Witt

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p] [PerfectRing k p]

theorem mem_span_or_isUnit (α : WittVector p k) :
    α ∈ Ideal.span {(p : WittVector p k)} ∨ IsUnit α := by
  by_cases hα : α = 0
  · exact Or.inl (hα ▸ Submodule.zero_mem _)
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' α hα
  rcases Nat.eq_zero_or_pos m with hm | hm
  · right
    rw [hu, hm, pow_zero, one_mul]
    exact Units.isUnit u
  · left
    rw [Ideal.mem_span_singleton]
    refine ⟨(p : WittVector p k) ^ (m - 1) * u, ?_⟩
    rw [hu, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]

theorem mem_span_of_mul_frobenius_eq (α c : WittVector p k)
    (h : α * WittVector.frobenius α = (p : WittVector p k) * c) :
    α ∈ Ideal.span {(p : WittVector p k)} := by
  rcases mem_span_or_isUnit α with hα | hα
  · exact hα
  exfalso
  have hw : IsUnit (α * WittVector.frobenius α) := hα.mul (hα.map _)
  rw [h] at hw
  exact (WittVector.irreducible p).not_isUnit (isUnit_of_mul_isUnit_left hw)

theorem intCast_mem_span_iff (n : ℤ) :
    (n : WittVector p k) ∈ Ideal.span {(p : WittVector p k)} ↔ (p : ℤ) ∣ n := by
  rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_intCast, CharP.intCast_eq_zero_iff k p]

end Witt

section Coord

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} [Fact q.Prime]
  {coord : ↥Λ → Zp2 q × Zp2 q}

noncomputable def coordHom (hcoord : IsOrderCoord Λ q coord) : ↥Λ →+ Zp2 q × Zp2 q :=
  AddMonoidHom.mk' coord hcoord.map_add

theorem coordHom_apply (hcoord : IsOrderCoord Λ q coord) (m : ↥Λ) : coordHom hcoord m = coord m := rfl

theorem coord_intCast (hcoord : IsOrderCoord Λ q coord) (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℤ)
    (h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0) := by
  have he : (⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ : ↥Λ) = n • (⟨1, hone⟩ : ↥Λ) := by
    apply Subtype.ext
    show ((n : ℚ) : ℍ[ℚ, a, b]) = ((n • (⟨1, hone⟩ : ↥Λ) : ↥Λ) : ℍ[ℚ, a, b])
    rw [Submodule.coe_smul, zsmul_eq_mul, mul_one, QuaternionAlgebra.coe_intCast]
  rw [← coordHom_apply hcoord, he, map_zsmul, coordHom_apply, hcoord.map_one hone, Prod.ext_iff]
  simp

theorem coord_star (hcoord : IsOrderCoord Λ q coord) (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ) (m : ↥Λ) (t : ℤ)
    (ht : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]))
    (hs : star (m : ℍ[ℚ, a, b]) ∈ Λ) :
    coord ⟨star (m : ℍ[ℚ, a, b]), hs⟩ = (WittVector.frobenius (coord m).1, -(coord m).2) := by
  have ht' : ((t : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [← ht]; exact Λ.add_mem m.2 hs
  have he : (⟨star (m : ℍ[ℚ, a, b]), hs⟩ : ↥Λ) = ⟨((t : ℚ) : ℍ[ℚ, a, b]), ht'⟩ - m := by
    apply Subtype.ext
    show star (m : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]) - m
    rw [← ht, add_sub_cancel_left]
  have htr := hcoord.trace m t ht
  rw [← coordHom_apply hcoord, he, map_sub, coordHom_apply, coordHom_apply, coord_intCast hcoord hone t ht',
    Prod.ext_iff]
  constructor
  · show (t : Zp2 q) - (coord m).1 = WittVector.frobenius (coord m).1
    rw [← htr, add_sub_cancel_left]
  · show (0 : Zp2 q) - (coord m).2 = -(coord m).2
    rw [zero_sub]

theorem coord_mul_star_fst (hcoord : IsOrderCoord Λ q coord) (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ) (m : ↥Λ) (t : ℤ)
    (ht : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]))
    (hs : star (m : ℍ[ℚ, a, b]) ∈ Λ) (hm : (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) ∈ Λ) :
    (coord ⟨(m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]), hm⟩).1 =
      (coord m).1 * WittVector.frobenius (coord m).1 -
        (q : Zp2 q) * ((coord m).2 * WittVector.frobenius (coord m).2) := by
  have := hcoord.map_mul m ⟨star (m : ℍ[ℚ, a, b]), hs⟩ hm
  rw [this, coord_star hcoord hone m t ht hs]
  simp only [map_neg]
  ring

theorem fst_mem_span_of_mul_star_eq (hcoord : IsOrderCoord Λ q coord) (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ) (m : ↥Λ)
    (t : ℤ) (ht : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]))
    (hs : star (m : ℍ[ℚ, a, b]) ∈ Λ) (n : ℤ)
    (hn : (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = ((((q : ℤ) * n : ℤ) : ℚ) : ℍ[ℚ, a, b])) :
    (coord m).1 ∈ Ideal.span {(q : Zp2 q)} := by
  have hm : (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [hn, QuaternionAlgebra.coe_intCast, ← zsmul_one]
    exact Λ.smul_mem _ hone
  have h1 := coord_mul_star_fst hcoord hone m t ht hs hm
  have h2 : coord ⟨(m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]), hm⟩ = ((((q : ℤ) * n : ℤ) : Zp2 q), 0) := by
    have hc : ((((q : ℤ) * n : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← hn]; exact hm
    have he : (⟨(m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) = ⟨_, hc⟩ := Subtype.ext hn
    rw [he, coord_intCast hcoord hone]
  rw [h2] at h1
  simp only at h1
  apply mem_span_of_mul_frobenius_eq (coord m).1 (n + (coord m).2 * WittVector.frobenius (coord m).2)
  have : (coord m).1 * WittVector.frobenius (coord m).1 =
      (((q : ℤ) * n : ℤ) : Zp2 q) + (q : Zp2 q) * ((coord m).2 * WittVector.frobenius (coord m).2) := by
    rw [h1]; ring
  rw [this]; push_cast; ring

end Coord

end E33W2

namespace E33W2

section Order

open QuaternionAlgebra

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} [Fact q.Prime] {coord : ↥Λ → Zp2 q × Zp2 q}

theorem star_mem (hΛ : IsOrder Λ) (m : ↥Λ) : star (m : ℍ[ℚ, a, b]) ∈ Λ :=
  (hΛ.star_mem_and_exists_int_trd_nrd m.2).1

theorem exists_trd_int (hΛ : IsOrder Λ) (m : ↥Λ) :
    ∃ t : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]) := by
  obtain ⟨-, t, -, ht, -⟩ := hΛ.star_mem_and_exists_int_trd_nrd m.2
  exact ⟨t, by rw [add_star_eq_coe_trd, ht]⟩

theorem exists_nrd_int (hΛ : IsOrder Λ) (m : ↥Λ) :
    ∃ N : ℤ, (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = ((N : ℚ) : ℍ[ℚ, a, b]) := by
  obtain ⟨-, -, N, -, hN⟩ := hΛ.star_mem_and_exists_int_trd_nrd m.2
  exact ⟨N, by rw [mul_star_eq_coe_nrd, hN]⟩

theorem normCoord (hΛ : IsOrder Λ) (hcoord : IsOrderCoord Λ q coord) (m : ↥Λ) (n : ℤ)
    (hm : (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((q : ℤ) * n : ℚ) : ℍ[ℚ, a, b])) :
    (coord m).1 ∈ Ideal.span {((q : ℕ) : Zp2 q)} := by
  obtain ⟨t, ht⟩ := exists_trd_int hΛ m
  have hm' : (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = ((((q : ℤ) * n : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
    rw [hm, Int.cast_mul]
  exact fst_mem_span_of_mul_star_eq hcoord hΛ.one_mem m t ht (star_mem hΛ m) n hm'

theorem exists_mul_star_eq_of_fst_mem_span (hΛ : IsOrder Λ) (hcoord : IsOrderCoord Λ q coord) (m : ↥Λ)
    (h1 : (coord m).1 ∈ Ideal.span {((q : ℕ) : Zp2 q)}) :
    ∃ n : ℤ, (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((q : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) := by
  obtain ⟨N, hN⟩ := exists_nrd_int hΛ m
  obtain ⟨t, ht⟩ := exists_trd_int hΛ m
  have hm : (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [hN, QuaternionAlgebra.coe_intCast, ← zsmul_one]
    exact Λ.smul_mem _ hΛ.one_mem
  have hf := coord_mul_star_fst hcoord hΛ.one_mem m t ht (star_mem hΛ m) hm
  have hc : ((N : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← hN]; exact hm
  have he : (⟨(m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) = ⟨_, hc⟩ := Subtype.ext hN
  rw [he, coord_intCast hcoord hΛ.one_mem] at hf
  simp only at hf
  have hmem : (N : Zp2 q) ∈ Ideal.span {(q : Zp2 q)} := by
    rw [hf]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  obtain ⟨n, hn⟩ := (intCast_mem_span_iff N).mp hmem
  exact ⟨n, by rw [hN, hn, Int.cast_mul]⟩

theorem primeElt (hΛ : IsOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hcoord : IsOrderCoord Λ q coord) (k : ℕ) :
    ∃ m : ↥Λ, (∃ n : ℤ, (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((q : ℤ) * n : ℚ) : ℍ[ℚ, a, b])) ∧
      (coord m).1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ k} ∧ (coord m).2 - 1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ k} := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  ·
    subst hk
    simp only [pow_zero, Ideal.span_singleton_one, Submodule.mem_top, and_true]
    refine ⟨⟨(((q : ℤ) : ℚ) : ℍ[ℚ, a, b]), hΛℤ q⟩, q, ?_⟩
    show (((q : ℤ) : ℚ) : ℍ[ℚ, a, b]) * star (((q : ℤ) : ℚ) : ℍ[ℚ, a, b]) = _
    rw [QuaternionAlgebra.star_coe, ← QuaternionAlgebra.coe_mul]
  · obtain ⟨m, h1, h2⟩ := hcoord.dense k 0 1
    rw [sub_zero] at h1
    refine ⟨m, ?_, h1, h2⟩
    apply exists_mul_star_eq_of_fst_mem_span hΛ hcoord m
    exact Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ hk.ne') h1

end Order

end E33W2

open scoped Quaternion
open CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

theorem solution
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {coord : ↥Λ → Zp2 r × Zp2 r} (hcoord : IsOrderCoord Λ r coord) (k : ℕ) :
    ∃ m : ↥Λ, (∃ n : ℤ, (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b])) ∧
      (coord m).1 ∈ Ideal.span {((r : ℕ) : Zp2 r) ^ k} ∧ (coord m).2 - 1 ∈ Ideal.span {((r : ℕ) : Zp2 r) ^ k} :=
  E33W2.primeElt hΛ hΛℤ hcoord k

end S_CerednikDrinfeld_QM_IsOrderCoord_exists_mul_star_eq_and_fst_mem_span_pow_and_snd_sub_one_mem_span_pow
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsOrderCoord_exists_mul_star_eq_and_fst_mem_span_pow_and_snd_sub_one_mem_span_pow (solution)
