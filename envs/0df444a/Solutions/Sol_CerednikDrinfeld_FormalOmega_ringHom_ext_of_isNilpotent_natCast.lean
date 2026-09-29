-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.ringHom_ext_of_isNilpotent_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e7b77d22-1d34-5941-8843-159a18eae09d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_ringHom_ext_of_isNilpotent_natCast

set_option autoImplicit false

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (C : Type) [CommRing C] (hC : IsNilpotent ((r : ℕ) : C)) (f g : 𝒪 →+* C) : f = g := by
  classical
  have hr : (r : ℕ).Prime := Fact.out

  have hrI : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.mem_span_singleton_self _
  have hI_ne_top : Ideal.span {π} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hπ.not_isUnit

  haveI : Nontrivial (𝒪 ⧸ Ideal.span {π}) := ⟨⟨0, 1, Ideal.Quotient.zero_ne_one_iff.2 hI_ne_top⟩⟩
  haveI hchar : CharP (𝒪 ⧸ Ideal.span {π}) r := by
    refine (CharP.charP_iff_prime_eq_zero hr).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq_zero_iff_mem]; exact hrI
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact hr.ne_zero)
  letI : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl r) (𝒪 ⧸ Ideal.span {π})) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨ZMod.castHom_injective (𝒪 ⧸ Ideal.span {π}), ?_⟩
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hres]
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have digit : ∀ x : 𝒪, ∃ (a : ℕ) (y : 𝒪), x = a + (r : 𝒪) * y := by
    intro x
    obtain ⟨z, hz⟩ := hbij.2 (Ideal.Quotient.mk (Ideal.span {π}) x)
    refine ⟨z.val, ?_⟩
    have hx : x - (z.val : 𝒪) ∈ Ideal.span {π} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_natCast, ← hz, ZMod.natCast_val, ZMod.castHom_apply, sub_self]
    rw [← hunr, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, by rw [mul_comm] at hy; rw [hy]; ring⟩

  have digits : ∀ (N : ℕ) (x : 𝒪), ∃ (n : ℕ) (y : 𝒪), x = n + (r : 𝒪) ^ N * y := by
    intro N
    induction N with
    | zero => intro x; exact ⟨0, x, by simp⟩
    | succ N ih =>
      intro x
      obtain ⟨a, y, hx⟩ := digit x
      obtain ⟨n, z, hy⟩ := ih y
      refine ⟨a + r * n, z, ?_⟩
      rw [hx, hy]; push_cast; ring

  obtain ⟨N, hN⟩ := hC
  apply RingHom.ext
  intro x
  obtain ⟨n, y, rfl⟩ := digits N x
  simp only [map_add, map_natCast, map_mul, map_pow, hN, zero_mul, add_zero]

end S_CerednikDrinfeld_FormalOmega_ringHom_ext_of_isNilpotent_natCast
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_ringHom_ext_of_isNilpotent_natCast (solution)
