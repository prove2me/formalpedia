-- Prove2me | solution 1 for CerednikDrinfeld.Onr.algHom_eq_of_comp_eq_of_sq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c352bdaa-9fee-5d55-95a1-452859420462

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Onr_algHom_eq_of_comp_eq_of_sq_zero

set_option autoImplicit false

namespace OnrRigid

open Polynomial

theorem pow_eq_self_of_card_eq {r : ℕ} [Fact r.Prime] (k : Type) [CommRing k] [Fintype k]
    (hk : Fintype.card k = r) (c : k) : c ^ r = c := by
  let e : ZMod r ≃+* k := ZMod.ringEquivOfPrime k Fact.out hk
  obtain ⟨z, rfl⟩ := e.surjective c
  rw [← map_pow, ZMod.pow_card]

theorem exists_iterate_eq_self_of_root {R : Type} [CommRing R] [IsDomain R] (F : R →+* R) (hF : Function.Injective F)
    (P : R[X]) (hP : P ≠ 0) (hPF : P.map F = P) (y : R) (hy : P.eval y = 0) :
    ∃ d : ℕ, 0 < d ∧ F^[d] y = y := by
  classical

  have horb : ∀ n : ℕ, P.eval (F^[n] y) = 0 := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h1 : (P.map F).eval (F (F^[n] y)) = F (P.eval (F^[n] y)) := by
        rw [Polynomial.eval_map, Polynomial.eval₂_hom]
      rw [hPF] at h1
      rw [h1, ih, map_zero]
  let S := P.roots.toFinset
  have hmem : ∀ n : ℕ, F^[n] y ∈ S := by
    intro n
    simp only [S, Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def]
    exact horb n
  let f : ℕ → S := fun n => ⟨F^[n] y, hmem n⟩
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hval : F^[i] y = F^[j] y := by
    simpa [f] using congrArg Subtype.val hfij

  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have hj : j = i + (j - i) := by omega
    rw [hj, Function.iterate_add_apply] at hval
    exact (Function.Injective.iterate hF i hval).symm
  · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_⟩
    have hi : i = j + (i - j) := by omega
    rw [hi, Function.iterate_add_apply] at hval
    exact Function.Injective.iterate hF j hval

theorem pow_pow_mul_eq_self {R : Type} [Monoid R] {y : R} {r d : ℕ} (h : y ^ (r ^ d) = y) (k : ℕ) :
    y ^ (r ^ (d * k)) = y := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

theorem sub_map_pow_succ {A C : Type} [CommRing A] [CommRing C] (ψ ψ' : A →+* C)
    (hsq : ∀ y z : A, (ψ y - ψ' y) * (ψ z - ψ' z) = 0) (y : A) (k : ℕ) :
    ψ (y ^ (k + 1)) - ψ' (y ^ (k + 1)) = (k + 1 : C) * ψ' y ^ k * (ψ y - ψ' y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h0 := hsq y y
    have e1 : ψ (y ^ (k + 1 + 1)) - ψ' (y ^ (k + 1 + 1)) =
        ψ y * (ψ (y ^ (k + 1)) - ψ' (y ^ (k + 1))) + (ψ y - ψ' y) * ψ' (y ^ (k + 1)) := by
      rw [pow_succ' y (k + 1), map_mul, map_mul]; ring
    rw [e1, ih, map_pow]
    push_cast
    linear_combination ((k : C) + 1) * ψ' y ^ k * h0

end OnrRigid

open OnrRigid Polynomial in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_prime : (Ideal.span {algebraMap 𝒪 Onr π}).IsPrime)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (C C₀ : Type) [CommRing C] [CommRing C₀] [Algebra 𝒪 C] [Algebra 𝒪 C₀] (hC : IsNilpotent (algebraMap 𝒪 C π))
    (p : C →ₐ[𝒪] C₀) (hsq : ∀ s t : C, p s = 0 → p t = 0 → s * t = 0)
    (ψ ψ' : Onr →ₐ[𝒪] C) (h : p.comp ψ = p.comp ψ') :
    ψ = ψ' := by
  classical
  have hr : r.Prime := Fact.out

  set I : Ideal Onr := Ideal.span {algebraMap 𝒪 Onr π} with hIdef
  haveI : I.IsPrime := hOnr_prime

  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hunr

  let φ : 𝒪 →+* Onr ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap 𝒪 Onr)
  have hφπ : φ π = 0 := by
    change Ideal.Quotient.mk I (algebraMap 𝒪 Onr π) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hφker : ∀ c ∈ Ideal.span ({π} : Set 𝒪), φ c = 0 := by
    intro c hc
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    rw [map_mul, hφπ, mul_zero]
  have hrR : ((r : ℕ) : Onr ⧸ I) = 0 := by
    rw [← map_natCast φ, ← ha]
    exact hφker _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  haveI : CharP (Onr ⧸ I) r := (CharP.charP_iff_prime_eq_zero hr).mpr hrR

  haveI : Finite (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) := Nat.finite_of_card_ne_zero (by rw [hres]; exact hr.ne_zero)
  letI : Fintype (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) := Fintype.ofFinite _
  have hcard : Fintype.card (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) = r := by
    rw [← Nat.card_eq_fintype_card, hres]
  have hφfix : ∀ c : 𝒪, (φ c) ^ r = φ c := by
    intro c
    have hlift : φ c = Ideal.Quotient.lift (Ideal.span ({π} : Set 𝒪)) φ hφker (Ideal.Quotient.mk _ c) := by
      rw [Ideal.Quotient.lift_mk]
    rw [hlift, ← map_pow, pow_eq_self_of_card_eq _ hcard]

  have hpow : ∀ x : Onr, ∃ d : ℕ, 0 < d ∧ (Ideal.Quotient.mk I x) ^ (r ^ d) = Ideal.Quotient.mk I x := by
    intro x
    obtain ⟨P, hPmonic, hPx⟩ := hOnr_alg x
    let F : Onr ⧸ I →+* Onr ⧸ I := frobenius (Onr ⧸ I) r
    have hF : Function.Injective F := frobenius_inj (Onr ⧸ I) r
    have hPbar_ne : P.map φ ≠ 0 := (hPmonic.map φ).ne_zero
    have hPbar_fix : (P.map φ).map F = P.map φ := by
      rw [Polynomial.map_map]
      refine Polynomial.ext fun i => ?_
      simp only [Polynomial.coeff_map, RingHom.comp_apply]
      exact hφfix _
    have hroot : (P.map φ).eval (Ideal.Quotient.mk I x) = 0 := by
      rw [Polynomial.eval_map]
      have : Ideal.Quotient.mk I (Polynomial.aeval x P) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hPx
      rwa [Polynomial.aeval_def, Polynomial.hom_eval₂] at this
    obtain ⟨d, hd, hdy⟩ := exists_iterate_eq_self_of_root F hF (P.map φ) hPbar_ne hPbar_fix _ hroot
    refine ⟨d, hd, ?_⟩
    rwa [iterate_frobenius] at hdy

  obtain ⟨n, hn⟩ := hC

  have hrC : ((r : ℕ) : C) ^ n = 0 := by
    have : ((r : ℕ) : C) = algebraMap 𝒪 C a * algebraMap 𝒪 C π := by
      rw [← map_natCast (algebraMap 𝒪 C), ← ha, map_mul]
    rw [this, mul_pow, hn, mul_zero]
  have hδker : ∀ y : Onr, p (ψ y - ψ' y) = 0 := by
    intro y
    have := congrArg (fun f : Onr →ₐ[𝒪] C₀ => f y) h
    simp only [AlgHom.comp_apply] at this
    rw [map_sub, this, sub_self]
  have hδsq : ∀ y z : Onr, (ψ y - ψ' y) * (ψ z - ψ' z) = 0 := fun y z => hsq _ _ (hδker y) (hδker z)

  have hstep : ∀ x : Onr, ∃ w : Onr, ψ x - ψ' x = algebraMap 𝒪 C π * (ψ w - ψ' w) := by
    intro x
    obtain ⟨d, hd, hdx⟩ := hpow x

    have hE : (Ideal.Quotient.mk I x) ^ (r ^ (d * n)) = Ideal.Quotient.mk I x := pow_pow_mul_eq_self hdx n
    have hEC : ((r ^ (d * n) : ℕ) : C) = 0 := by
      rw [mul_comm, pow_mul]; push_cast; rw [hrC, zero_pow hd.ne']
    obtain ⟨E', hE'⟩ : ∃ E' : ℕ, r ^ (d * n) = E' + 1 :=
      Nat.exists_eq_add_one_of_ne_zero (pow_pos hr.pos _).ne'
    have hmem : x - x ^ (r ^ (d * n)) ∈ I := by
      rw [← Ideal.Quotient.eq, map_pow, hE]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨w, ?_⟩
    have hx : x = x ^ (E' + 1) + w * algebraMap 𝒪 Onr π := by rw [← hE', hw]; ring
    have hpowδ := sub_map_pow_succ ψ.toRingHom ψ'.toRingHom hδsq x E'
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hpowδ
    have hE'C : ((E' : C) + 1) = 0 := by exact_mod_cast (hE' ▸ hEC)
    calc ψ x - ψ' x
        = (ψ (x ^ (E' + 1)) - ψ' (x ^ (E' + 1))) + (ψ (w * algebraMap 𝒪 Onr π) - ψ' (w * algebraMap 𝒪 Onr π)) := by
          conv_lhs => rw [hx]
          rw [map_add, map_add]; ring
      _ = 0 + algebraMap 𝒪 C π * (ψ w - ψ' w) := by
          rw [hpowδ, hE'C, zero_mul, zero_mul, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
          ring
      _ = algebraMap 𝒪 C π * (ψ w - ψ' w) := zero_add _

  have hiter : ∀ (j : ℕ) (x : Onr), ∃ w : Onr, ψ x - ψ' x = algebraMap 𝒪 C π ^ j * (ψ w - ψ' w) := by
    intro j
    induction j with
    | zero => intro x; exact ⟨x, by simp⟩
    | succ j ih =>
      intro x
      obtain ⟨w, hw⟩ := ih x
      obtain ⟨w', hw'⟩ := hstep w
      exact ⟨w', by rw [hw, hw', pow_succ]; ring⟩

  refine AlgHom.ext fun x => ?_
  obtain ⟨w, hw⟩ := hiter n x
  rw [hn, zero_mul] at hw
  exact sub_eq_zero.mp hw

end S_CerednikDrinfeld_Onr_algHom_eq_of_comp_eq_of_sq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_Onr_algHom_eq_of_comp_eq_of_sq_zero (solution)
