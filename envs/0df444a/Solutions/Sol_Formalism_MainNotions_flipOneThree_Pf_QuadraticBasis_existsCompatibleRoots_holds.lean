-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.existsCompatibleRoots_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:44.937987+00:00
-- url     : https://prove2.me/submissions/c1c0d126-8702-4a1c-9201-a638e73261b8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
open Polynomial
private theorem qr_fix {F k : Type} [Field F] [Field k] [Fintype F] (ι : F →+* k) (q : ℕ)
    (hF : Fintype.card F = q) (hq : 1 < q) (x : k) (hx : x ^ q = x) : ∃ y, ι y = x := by
  classical
  have hP : (X ^ q - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq
  have hroot : ∀ z : k, z ^ q = z → z ∈ (X ^ q - X : k[X]).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot, eval_sub, eval_pow, eval_X, hz, sub_self]
  have hsub : Finset.univ.image ι ⊆ (X ^ q - X : k[X]).roots.toFinset := by
    intro z hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hz
    apply hroot
    rw [← map_pow, ← hF, FiniteField.pow_card]
  have hle : (X ^ q - X : k[X]).roots.toFinset.card ≤ (Finset.univ.image ι).card := by
    rw [Finset.card_image_of_injective _ ι.injective, Finset.card_univ, hF]
    calc _ ≤ Multiset.card (X ^ q - X : k[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ q - X : k[X]).natDegree := card_roots' _
      _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq k hq
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hx' := hroot x hx
  rw [← heq] at hx'
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hx'
  exact ⟨y, hy⟩
private theorem qr_exists {F k : Type} [Field F] [Field k] [Fintype F] [Fintype k] (ι : F →+* k) (p n : ℕ)
    [Fact p.Prime] [CharP k p] (hF : Fintype.card F = p ^ n) (hk : Fintype.card k = (p ^ n) ^ 2)
    (hq : 1 < p ^ n) :
    ∃ b c : F, (X ^ 2 + C b * X + C c : F[X]) ∣ X ^ ((p ^ n) ^ 2) - X ∧ ∀ x : F, x ^ 2 + b * x + c ≠ 0 := by
  classical
  have hq2 : p ^ n < (p ^ n) ^ 2 := by nlinarith
  obtain ⟨t, ht⟩ : ∃ t : k, ∀ y, ι y ≠ t := by
    by_contra h
    push_neg at h
    have := Fintype.card_le_of_surjective ι h
    rw [hF, hk] at this
    exact absurd this (not_le.mpr hq2)
  have hφ : ∀ x : k, iterateFrobenius k p n x = x ^ (p ^ n) := fun x => iterateFrobenius_def p n x
  have htq : t ^ ((p ^ n) ^ 2) = t := by rw [← hk]; exact FiniteField.pow_card t
  have hqq : ∀ x : k, (x ^ (p ^ n)) ^ (p ^ n) = x ^ ((p ^ n) ^ 2) := fun x => by rw [← pow_mul, sq]
  have hne : t ^ (p ^ n) ≠ t := fun h => by
    obtain ⟨y, hy⟩ := qr_fix ι (p ^ n) hF hq t h
    exact ht y hy
  obtain ⟨b, hb⟩ := qr_fix ι (p ^ n) hF hq (-(t + t ^ (p ^ n))) (by
    have h := hφ (-(t + t ^ (p ^ n)))
    rw [map_neg, map_add, hφ, hφ, hqq, htq] at h
    rw [← h]; ring)
  obtain ⟨c, hc⟩ := qr_fix ι (p ^ n) hF hq (t * t ^ (p ^ n)) (by
    rw [mul_pow, hqq, htq, mul_comm])
  have hmonic : (X ^ 2 + C b * X + C c : F[X]).Monic := by monicity!
  have hmap : (X ^ 2 + C b * X + C c : F[X]).map ι = (X - C t) * (X - C (t ^ (p ^ n))) := by
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, hb, hc, map_neg,
      map_add, map_mul]
    ring
  have hQ : (X ^ ((p ^ n) ^ 2) - X : F[X]).map ι = (X ^ ((p ^ n) ^ 2) - X : k[X]) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X]
  refine ⟨b, c, ?_, ?_⟩
  · rw [← Polynomial.map_dvd_map ι ι.injective hmonic, hmap, hQ]
    have hcop : IsCoprime (X - C t) (X - C (t ^ (p ^ n))) :=
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne.symm).isUnit
    refine hcop.mul_dvd ?_ ?_
    · rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_X, htq, sub_self]
    · rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_X, ← pow_mul, mul_comm, pow_mul, htq, sub_self]
  · intro x hx
    have h1 : (ι x - t) * (ι x - t ^ (p ^ n)) = 0 := by
      have h := congrArg ι hx
      rw [map_add, map_add, map_mul, map_pow, hb, hc, map_zero] at h
      linear_combination h
    rcases mul_eq_zero.mp h1 with h | h
    · exact ht x (sub_eq_zero.mp h)
    · apply ht (x ^ (p ^ n))
      rw [map_pow, sub_eq_zero.mp h, hqq, htq]
private theorem qr_root {F k : Type} [Field F] [Field k] [Fintype k] (ι : F →+* k) (p n : ℕ)
    [Fact p.Prime] [CharP k p] (hn : 0 < n) (hk : Fintype.card k = (p ^ n) ^ 2) (b c : F)
    (hdvd : (X ^ 2 + C b * X + C c : F[X]) ∣ X ^ ((p ^ n) ^ 2) - X) (hno : ∀ x : F, x ^ 2 + b * x + c ≠ 0) :
    ∃ t : k, t ^ 2 + ι b * t + ι c = 0 ∧ 2 * t + ι b ≠ 0 ∧ ∀ y, ι y ≠ t := by
  classical
  have hp : p.Prime := Fact.out
  have h1q : 1 < Fintype.card k := by
    have : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.one_lt
    rw [hk]; nlinarith
  have hQ0 : (X ^ ((p ^ n) ^ 2) - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k (hk ▸ h1q)
  have hdvd' : (X ^ 2 + C (ι b) * X + C (ι c) : k[X]) ∣ X ^ ((p ^ n) ^ 2) - X := by
    have h := Polynomial.map_dvd ι hdvd
    simpa using h
  have hsplitQ : (X ^ ((p ^ n) ^ 2) - X : k[X]).Splits := by
    rw [← hk, splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq k h1q]
    simp
  have hsplitP := Splits.of_dvd hsplitQ hQ0 hdvd'
  have hdegP : (X ^ 2 + C (ι b) * X + C (ι c) : k[X]).natDegree = 2 := by compute_degree!
  have hP0 : (X ^ 2 + C (ι b) * X + C (ι c) : k[X]) ≠ 0 := fun h => by rw [h] at hdegP; simp at hdegP
  rw [splits_iff_card_roots, hdegP] at hsplitP
  obtain ⟨t, ht⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hsplitP]; norm_num)
  rw [mem_roots hP0, IsRoot, eval_add, eval_add, eval_mul, eval_pow, eval_C, eval_C, eval_X] at ht
  refine ⟨t, ht, ?_, ?_⟩
  · intro h2
    have hsq : (X ^ 2 + C (ι b) * X + C (ι c) : k[X]) = (X - C t) * (X - C t) := by
      have hb' : ι b = -2 * t := by linear_combination h2
      have hc' : ι c = t ^ 2 := by linear_combination ht - t * h2
      rw [hb', hc']
      simp only [map_mul, map_neg, map_pow, map_ofNat]
      ring
    have hsf := (galois_poly_separable p ((p ^ n) ^ 2) (dvd_pow (dvd_pow_self p hn.ne') two_ne_zero) :
      (X ^ ((p ^ n) ^ 2) - X : k[X]).Separable).squarefree
    rw [hsq] at hdvd'
    exact Polynomial.not_isUnit_X_sub_C t (hsf _ hdvd')
  · intro y hy
    apply hno y
    apply ι.injective
    rw [map_add, map_add, map_mul, map_pow, hy, map_zero]
    exact ht
private theorem qr_hensel {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (w : O) (hw : Irreducible w) (B D a₀ : O)
    (h1 : w ∣ a₀ ^ 2 + B * a₀ + D) (h2 : ¬ w ∣ 2 * a₀ + B) :
    ∃ θ : O, θ ^ 2 + B * θ + D = 0 ∧ w ∣ θ - a₀ := by
  haveI := hc
  haveI := IsAdicComplete.henselianRing O (IsLocalRing.maximalIdeal O)
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer w).mp hw
  have hd : eval a₀ (derivative (X ^ 2 + C B * X + C D)) = 2 * a₀ + B := by
    simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul,
      eval_C, eval_X, eval_pow, eval_zero, eval_one, eval_natCast, zero_mul, mul_one, add_zero, zero_add]
    (try norm_num) <;> ring
  obtain ⟨θ, hθ, hθa⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal O)
    (X ^ 2 + C B * X + C D) (by monicity!) a₀
    (by rw [hmax, Ideal.mem_span_singleton]; simpa using h1)
    (by rw [hd]
        exact (IsLocalRing.notMem_maximalIdeal.mp (by rw [hmax, Ideal.mem_span_singleton]; exact h2)).map _)
  refine ⟨θ, ?_, ?_⟩
  · simpa [IsRoot] using hθ
  · rw [hmax, Ideal.mem_span_singleton] at hθa
    exact hθa
private theorem qr_transport (p n : ℕ) {W₁ W₂ : Type} [CommRing W₁] [CommRing W₂] (φ : W₁ ≃+* W₂) (b c : W₁)
    (h : qrGood p n W₁ b c) : qrGood p n W₂ (φ b) (φ c) := by
  unfold qrGood at h ⊢
  obtain ⟨hd, hr⟩ := h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (W₁ ⧸ Ideal.span {(p : W₁)}) ≃+* (W₂ ⧸ Ideal.span {(p : W₂)}),
      ∀ x, ψ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (φ x) :=
    ⟨Ideal.quotientEquiv _ _ φ (by rw [Ideal.map_span, Set.image_singleton]; simp),
      fun x => by first | exact Ideal.quotientEquiv_mk _ _ _ _ x | simp [Ideal.quotientEquiv_mk] | rfl⟩
  refine ⟨?_, ?_⟩
  · have h := Polynomial.map_dvd (ψ : (W₁ ⧸ Ideal.span {(p : W₁)}) →+* (W₂ ⧸ Ideal.span {(p : W₂)})) hd
    simpa [hψ] using h
  · intro x hx
    apply hr (ψ.symm x)
    apply ψ.injective
    rw [map_add, map_add, map_mul, map_pow, hψ, hψ, RingEquiv.apply_symm_apply, map_zero]
    exact hx
private theorem qr_side (p n : ℕ) (hp : p.Prime) (hn : 0 < n) (W O : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (j : W →+* O) (w : O)
    (hpW : Irreducible (p : W)) (hcW : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n)
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (hw2 : w ^ 2 = (p : O)) (hw : Irreducible w)
    (hcO : Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n)) :
    (∃ b c : W, qrGood p n W b c) ∧
      ∀ b c : W, qrGood p n W b c → ∃ θ : O, θ ^ 2 + j b * θ + j c = 0 ∧ ∀ a : W, ¬ w ∣ θ - j a := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (Ideal.span {(p : W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpW
  haveI : (Ideal.span {w}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hw
  letI : Field (W ⧸ Ideal.span {(p : W)}) := Ideal.Quotient.field _
  letI : Field (O ⧸ Ideal.span {w}) := Ideal.Quotient.field _
  haveI : Finite (W ⧸ Ideal.span {(p : W)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcW]; exact (pow_pos hp.pos _).ne')
  haveI : Finite (O ⧸ Ideal.span {w}) :=
    Nat.finite_of_card_ne_zero (by rw [hcO]; exact (pow_pos hp.pos _).ne')
  letI : Fintype (W ⧸ Ideal.span {(p : W)}) := Fintype.ofFinite _
  letI : Fintype (O ⧸ Ideal.span {w}) := Fintype.ofFinite _
  have hFc : Fintype.card (W ⧸ Ideal.span {(p : W)}) = p ^ n := by rw [← Nat.card_eq_fintype_card, hcW]
  have hkc : Fintype.card (O ⧸ Ideal.span {w}) = (p ^ n) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hcO]; ring
  haveI : CharP (O ⧸ Ideal.span {w}) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {w})), ← hw2, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    exact dvd_pow_self w two_ne_zero)
  obtain ⟨ι, hι⟩ : ∃ ι : (W ⧸ Ideal.span {(p : W)}) →+* (O ⧸ Ideal.span {w}),
      ∀ a, ι (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (j a) :=
    ⟨Ideal.Quotient.lift _ ((Ideal.Quotient.mk (Ideal.span {w})).comp j) (by
      intro a ha
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp ha
      rw [RingHom.comp_apply, map_mul, map_natCast, ← hw2, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact dvd_mul_of_dvd_left (dvd_pow_self w two_ne_zero) _), fun a => rfl⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨b₀, c₀, hd, hr⟩ := qr_exists ι p n hFc hkc (Nat.one_lt_pow hn.ne' hp.one_lt)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b₀
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c₀
    exact ⟨b, c, by unfold qrGood; exact ⟨hd, hr⟩⟩
  · intro b c hg
    unfold qrGood at hg
    obtain ⟨hd, hr⟩ := hg
    obtain ⟨t, ht, ht2, htn⟩ := qr_root ι p n hn hkc (Ideal.Quotient.mk _ b) (Ideal.Quotient.mk _ c) hd hr
    obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨θ, hθ, hθa⟩ := qr_hensel hc w hw (j b) (j c) a₀
      (by rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]; simpa [hι] using ht)
      (by
        intro hdv
        apply ht2
        have e : Ideal.Quotient.mk (Ideal.span {w}) (2 * a₀ + j b) =
            2 * Ideal.Quotient.mk (Ideal.span {w}) a₀ + ι (Ideal.Quotient.mk _ b) := by
          rw [hι, map_add, map_mul]
          first | rfl | (rw [map_ofNat]) | norm_num | simp
        rw [← e, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
        exact hdv)
    refine ⟨θ, hθ, fun a ha => htn (Ideal.Quotient.mk _ a) ?_⟩
    rw [hι, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    have h := dvd_sub hθa ha
    rwa [sub_sub_sub_cancel_left] at h
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
end

set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
open Polynomial
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution : QuadRoots := by
  intro p n hp hn W₁ W₂ O₁ O₂ _ _ _ _ _ _ _ _ _ _ _ _ j₁ j₂ w₁ w₂ hpW₁ hpW₂ hcW₁ hcW₂ hc₁ hc₂ hw2₁ hw2₂
    hw₁ hw₂ hcO₁ hcO₂ φW
  obtain ⟨⟨b, c, hg⟩, h1⟩ := qr_side p n hp hn W₁ O₁ j₁ w₁ hpW₁ hcW₁ hc₁ hw2₁ hw₁ hcO₁
  obtain ⟨-, h2⟩ := qr_side p n hp hn W₂ O₂ j₂ w₂ hpW₂ hcW₂ hc₂ hw2₂ hw₂ hcO₂
  obtain ⟨θ₁, e1, n1⟩ := h1 b c hg
  obtain ⟨θ₂, e2, n2⟩ := h2 (φW b) (φW c) (qr_transport p n φW b c hg)
  exact ⟨c, b, θ₁, θ₂, e1, e2, n1, n2⟩
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
