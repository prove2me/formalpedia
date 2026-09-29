-- Prove2me | solution 1 for CerednikDrinfeld.dvd_of_forall_frobenius_zpow_apply_eq_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c0ad8252-6d8a-58bf-aed1-abb9151d202c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_dvd_of_forall_frobenius_zpow_apply_eq_of_fixed

set_option autoImplicit false

open Polynomial

namespace FrobOrder

theorem pow_pow_pow_eq_self {K : Type} [Monoid K] (x : K) (q : ℕ) (hx : x ^ q = x) (n : ℕ) : x ^ q ^ n = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, hx]

theorem natDegree_X_pow_sub_X (K : Type) [Field K] (q : ℕ) (hq : 1 < q) : (X ^ q - X : K[X]).natDegree = q := by
  rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hq]

theorem X_pow_sub_X_ne_zero (K : Type) [Field K] (q : ℕ) (hq : 1 < q) : (X ^ q - X : K[X]) ≠ 0 := by
  intro h; have := natDegree_X_pow_sub_X K q hq; rw [h, natDegree_zero] at this; omega

theorem mem_roots_toFinset_iff (K : Type) [Field K] [DecidableEq K] (q : ℕ) (hq : 1 < q) (x : K) :
    x ∈ (X ^ q - X : K[X]).roots.toFinset ↔ x ^ q = x := by
  rw [Multiset.mem_toFinset, mem_roots (X_pow_sub_X_ne_zero K q hq), IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]

theorem card_roots_toFinset (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (d : ℕ) (hd : 0 < d) : ((X ^ r ^ d - X : K[X]).roots.toFinset).card = r ^ d := by
  have hr : r.Prime := Fact.out
  have h1 : 1 < r ^ d := Nat.one_lt_pow hd.ne' hr.one_lt
  have hsep : (X ^ r ^ d - X : K[X]).Separable := galois_poly_separable r (r ^ d) (dvd_pow_self r hd.ne')
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep)]
  have := (IsAlgClosed.splits (X ^ r ^ d - X : K[X])).natDegree_eq_card_roots
  rw [natDegree_X_pow_sub_X K _ h1] at this
  exact this.symm

theorem card_roots_toFinset_le (K : Type) [Field K] [DecidableEq K] (q : ℕ) (hq : 1 < q) :
    ((X ^ q - X : K[X]).roots.toFinset).card ≤ q := by
  calc ((X ^ q - X : K[X]).roots.toFinset).card ≤ (X ^ q - X : K[X]).roots.card := Multiset.toFinset_card_le _
    _ ≤ (X ^ q - X : K[X]).natDegree := card_roots' _
    _ = q := natDegree_X_pow_sub_X K q hq

theorem dvd_of_forall_pow_eq (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) [Fact r.Prime] [CharP K r] (d m : ℕ)
    (h : ∀ x : K, x ^ r ^ d = x → x ^ r ^ m = x) : d ∣ m := by
  classical
  have hr : r.Prime := Fact.out
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·
    subst hd
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm]
    · exfalso
      have h1 : 1 < r ^ m := Nat.one_lt_pow hm.ne' hr.one_lt
      have hall : ∀ x : K, x ∈ (X ^ r ^ m - X : K[X]).roots.toFinset := fun x =>
        (mem_roots_toFinset_iff K (r ^ m) h1 x).mpr (h x (by simp))
      have hfin : (Set.univ : Set K).Finite :=
        (X ^ r ^ m - X : K[X]).roots.toFinset.finite_toSet.subset fun x _ => hall x
      exact Set.infinite_univ (α := K) hfin
  ·
    have hdiv := Nat.div_add_mod m d
    set q := m / d with hq
    set s := m % d with hs
    have hsd : s < d := Nat.mod_lt m hd
    suffices hs0 : s = 0 by exact ⟨q, by omega⟩
    by_contra hs0
    have hs1 : 0 < s := Nat.pos_of_ne_zero hs0
    have h1d : 1 < r ^ d := Nat.one_lt_pow hd.ne' hr.one_lt
    have h1s : 1 < r ^ s := Nat.one_lt_pow hs1.ne' hr.one_lt
    have hsub : (X ^ r ^ d - X : K[X]).roots.toFinset ⊆ (X ^ r ^ s - X : K[X]).roots.toFinset := by
      intro x hx
      rw [mem_roots_toFinset_iff K _ h1d] at hx
      rw [mem_roots_toFinset_iff K _ h1s]
      have hm := h x hx

      have e1 : x ^ r ^ (d * q) = x := by rw [pow_mul]; exact pow_pow_pow_eq_self x (r ^ d) hx q
      rw [← hdiv, pow_add, pow_mul, e1] at hm
      exact hm
    have := Finset.card_le_card hsub
    rw [card_roots_toFinset K r d hd] at this
    have := this.trans (card_roots_toFinset_le K (r ^ s) h1s)
    exact absurd this (not_le.mpr (Nat.pow_lt_pow_right hr.one_lt hsd))

end FrobOrder

namespace FrobOrderAbs

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr]

theorem map_mem_span (Fr : Onr ≃ₐ[𝒪] Onr) (π : 𝒪) {t : Onr} (ht : t ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    Fr t ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  rw [map_mul, AlgEquiv.commutes]
  exact Ideal.mem_span_singleton'.mpr ⟨Fr c, rfl⟩

theorem zpow_natCast_apply_sub_pow_mem (Fr : Onr ≃ₐ[𝒪] Onr) (π : 𝒪) (r : ℕ)
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π}) (n : ℕ) (x : Onr) :
    (Fr ^ (n : ℤ)) x - x ^ r ^ n ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, zpow_add_one, AlgEquiv.mul_apply]

    have h1 : (Fr ^ (n : ℤ)) (Fr x) - (Fr x) ^ r ^ n ∈ Ideal.span {algebraMap 𝒪 Onr π} := ih (Fr x)
    have h2 : (Fr x) ^ r ^ n - (x ^ r) ^ r ^ n ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
      have := (Ideal.Quotient.eq (I := Ideal.span {algebraMap 𝒪 Onr π})).mpr (hFr x)
      apply (Ideal.Quotient.eq (I := Ideal.span {algebraMap 𝒪 Onr π})).mp
      rw [map_pow, map_pow, this]
    have := Ideal.add_mem _ h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ'] at this
    exact this

theorem zpow_apply_eq_self' {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (σ : A ≃ₐ[R] A) (y : A)
    (h : σ y = y) (n : ℤ) : (σ ^ n) y = y := by
  have hinv : σ⁻¹ y = y := by
    conv_lhs => rw [← h]
    exact σ.symm_apply_apply y
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, h, ih]
  | pred n ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih]

end FrobOrderAbs

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (π : 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (k : Type) [Field k] [Algebra 𝒪 k] (ψ : Onr →ₐ[𝒪] k) (d m : ℤ)
    (h : ∀ y : Onr, (Fr ^ d) y = y → ψ ((Fr ^ m) y) = ψ y) : d ∣ m := by
  classical
  have hr : r.Prime := Fact.out
  set I : Ideal Onr := Ideal.span {algebraMap 𝒪 Onr π} with hI
  haveI hImax : I.IsMaximal := hOnr_max
  letI : Field (Onr ⧸ I) := Ideal.Quotient.field I
  haveI := hOnr_complete

  have hrI : ((r : ℕ) : Onr) ∈ I := by
    have : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    rw [hI, Ideal.mem_span_singleton']
    exact ⟨algebraMap 𝒪 Onr c, by rw [← map_mul, hc, map_natCast]⟩
  haveI hchar : CharP (Onr ⧸ I) r := by
    apply (CharP.charP_iff_prime_eq_zero hr).mpr
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hrI

  haveI halg : IsAlgClosed (Onr ⧸ I) := by
    apply IsAlgClosed.of_exists_root
    intro q hqm hqirr
    obtain ⟨Q, hQmap, hQdeg, hQmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.lifts_iff_coeff_lifts q).mpr fun n => Ideal.Quotient.mk_surjective (q.coeff n)) hqm
    have hQpos : 0 < Q.natDegree := by rw [hQdeg]; exact hqirr.natDegree_pos
    obtain ⟨x, hx⟩ := hOnr_closed Q hQmonic hQpos
    refine ⟨Ideal.Quotient.mk I x, ?_⟩
    rw [← hQmap, eval_map, eval₂_hom, Ideal.Quotient.eq_zero_iff_mem]
    exact hx

  have hunit : ∀ z : Onr, z ∉ I → IsUnit z := by
    intro z hz
    have hz' : Ideal.Quotient.mk I z ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk I z)⁻¹
    have ht : z * w - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hw, mul_inv_cancel₀ hz', sub_self]
    have hjac : z * w - 1 ∈ (⊥ : Ideal Onr).jacobson := IsAdicComplete.le_jacobson_bot I ht
    have hu : IsUnit ((z * w - 1) * 1 + 1) := Ideal.mem_jacobson_bot.mp hjac 1
    rw [mul_one, sub_add_cancel] at hu
    exact isUnit_of_mul_isUnit_left hu

  have hsep : ∀ (e : ℕ), 0 < e → ∀ y₁ y₂ : Onr, y₁ ^ r ^ e = y₁ → y₂ ^ r ^ e = y₂ → y₂ - y₁ ∈ I → y₂ = y₁ := by
    intro e he y₁ y₂ h₁ h₂ h12
    set q := r ^ e with hq
    have hgeom := Commute.geom_sum₂_mul (Commute.all y₂ y₁) q
    rw [h₁, h₂] at hgeom

    have hS : ((∑ i ∈ Finset.range q, y₂ ^ i * y₁ ^ (q - 1 - i)) - 1) * (y₂ - y₁) = 0 := by rw [sub_mul, one_mul, hgeom, sub_self]
    rcases mul_eq_zero.mp hS with h | h
    ·
      exfalso
      have hSI : (∑ i ∈ Finset.range q, y₂ ^ i * y₁ ^ (q - 1 - i)) ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        have hyy : Ideal.Quotient.mk I y₂ = Ideal.Quotient.mk I y₁ := by rw [Ideal.Quotient.eq]; exact h12
        have : ∀ i ∈ Finset.range q, Ideal.Quotient.mk I (y₂ ^ i * y₁ ^ (q - 1 - i)) = Ideal.Quotient.mk I y₁ ^ (q - 1) := by
          intro i hi
          rw [map_mul, map_pow, map_pow, hyy, ← pow_add]
          congr 1; rw [Finset.mem_range] at hi; omega
        rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have : ((q : ℕ) : Onr ⧸ I) = 0 := by
          rw [hq, Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne']
        rw [this, zero_mul]
      have : (1 : Onr) ∈ I := by
        have := Ideal.sub_mem I hSI (show (∑ i ∈ Finset.range q, y₂ ^ i * y₁ ^ (q - 1 - i)) - 1 ∈ I by rw [h]; exact I.zero_mem)
        rwa [sub_sub_cancel] at this
      exact hImax.ne_top ((Ideal.eq_top_iff_one _).mpr this)
    · exact sub_eq_zero.mp h

  have key : ∀ (e M : ℕ), 0 < e → (∀ y : Onr, (Fr ^ (e : ℤ)) y = y → ψ ((Fr ^ (M : ℤ)) y) = ψ y) →
      ∀ x : Onr ⧸ I, x ^ r ^ e = x → x ^ r ^ M = x := by
    intro e M he hψ x hx
    set q := r ^ e with hq
    have hq1 : 1 < q := Nat.one_lt_pow he.ne' hr.one_lt

    obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective x
    set F : Onr[X] := X ^ q - X with hF
    have hFmonic : F.Monic := by
      rw [hF]; exact (monic_X_pow q).sub_of_left (by rw [degree_X_pow, degree_X]; exact_mod_cast hq1)
    have hFeval : ∀ z : Onr, F.eval z = z ^ q - z := by intro z; simp [hF]
    have hFa₀ : F.eval a₀ ∈ I := by
      rw [hFeval, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ha₀, hx, sub_self]
    have hFder : IsUnit (Ideal.Quotient.mk I (F.derivative.eval a₀)) := by
      have : F.derivative.eval a₀ = (q : Onr) * a₀ ^ (q - 1) - 1 := by
        rw [hF, derivative_sub, derivative_X_pow, derivative_X]; simp
      rw [this, map_sub, map_mul, map_natCast, map_one, hq, Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne', zero_mul, zero_sub]
      exact isUnit_one.neg
    obtain ⟨y, hyroot, hya₀⟩ := HenselianRing.is_henselian F hFmonic a₀ hFa₀ hFder
    have hyq : y ^ q = y := by have := hyroot; rw [IsRoot.def, hFeval, sub_eq_zero] at this; exact this
    have hmy : Ideal.Quotient.mk I y = x := by rw [← ha₀, Ideal.Quotient.eq]; exact hya₀

    have hroot_pow : ∀ n : ℕ, ((Fr ^ (n : ℤ)) y) ^ q = (Fr ^ (n : ℤ)) y := by
      intro n; rw [← map_pow, hyq]

    have hfix : (Fr ^ (e : ℤ)) y = y := by
      apply hsep e he y _ hyq (hroot_pow e)
      have h1 := FrobOrderAbs.zpow_natCast_apply_sub_pow_mem Fr π r hFr e y
      rw [← hq, hyq] at h1; exact h1

    have hψy := hψ y hfix
    have hM : (Fr ^ (M : ℤ)) y = y := by
      by_contra hne
      have hnotin : (Fr ^ (M : ℤ)) y - y ∉ I := fun hin => hne (hsep e he y _ hyq (hroot_pow M) hin)
      obtain ⟨u, hu⟩ := hunit _ hnotin
      have : ψ ((Fr ^ (M : ℤ)) y - y) = 0 := by rw [map_sub, hψy, sub_self]
      rw [← hu] at this
      exact (Units.map (ψ : Onr →* k) u).ne_zero this

    have h1 := FrobOrderAbs.zpow_natCast_apply_sub_pow_mem Fr π r hFr M y
    rw [hM] at h1
    have : Ideal.Quotient.mk I y = Ideal.Quotient.mk I (y ^ r ^ M) := by rw [Ideal.Quotient.eq]; exact h1
    rw [map_pow, hmy] at this
    exact this.symm

  set D := d.natAbs with hD
  set M := m.natAbs with hM
  have hfixD : ∀ y : Onr, (Fr ^ (D : ℤ)) y = y ↔ (Fr ^ d) y = y := by
    intro y
    rcases Int.natAbs_eq d with hd | hd
    · rw [← hd]
    · have e : Fr ^ d = (Fr ^ (D : ℤ))⁻¹ := by rw [hd, zpow_neg]
      rw [e]
      constructor
      · intro hy
        have := FrobOrderAbs.zpow_apply_eq_self' (Fr ^ (D : ℤ)) y hy (-1)
        rwa [zpow_neg_one] at this
      · intro hy
        have := FrobOrderAbs.zpow_apply_eq_self' ((Fr ^ (D : ℤ))⁻¹) y hy (-1)
        rwa [zpow_neg_one, inv_inv] at this
  have hψM : ∀ y : Onr, (Fr ^ (D : ℤ)) y = y → ψ ((Fr ^ (M : ℤ)) y) = ψ y := by
    intro y hy
    have hyd : (Fr ^ d) y = y := (hfixD y).mp hy
    rcases Int.natAbs_eq m with hm' | hm'
    · rw [← hm']; exact h y hyd
    ·
      have hy' : (Fr ^ d) ((Fr ^ (M : ℤ)) y) = (Fr ^ (M : ℤ)) y := by
        rw [← AlgEquiv.mul_apply, zpow_mul_comm, AlgEquiv.mul_apply, hyd]
      have := h _ hy'
      rw [hm', ← AlgEquiv.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, AlgEquiv.one_apply] at this
      exact this.symm

  suffices hDM : D ∣ M by exact Int.natAbs_dvd_natAbs.mp hDM
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  ·
    rw [hD0]
    have hall : ∀ y : Onr, ψ ((Fr ^ (M : ℤ)) y) = ψ y := fun y => hψM y (by rw [hD0, Nat.cast_zero, zpow_zero, AlgEquiv.one_apply])
    have hsub := key (M + 1) M (Nat.succ_pos M) (fun y _ => hall y)
    have hdvd : M + 1 ∣ M := FrobOrder.dvd_of_forall_pow_eq (Onr ⧸ I) r (M + 1) M hsub
    have : M = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (Nat.lt_succ_self M)
    rw [this]
  · exact FrobOrder.dvd_of_forall_pow_eq (Onr ⧸ I) r D M (key D M hDpos hψM)

end S_CerednikDrinfeld_dvd_of_forall_frobenius_zpow_apply_eq_of_fixed
end P2MW
export P2MW.S_CerednikDrinfeld_dvd_of_forall_frobenius_zpow_apply_eq_of_fixed (solution)
