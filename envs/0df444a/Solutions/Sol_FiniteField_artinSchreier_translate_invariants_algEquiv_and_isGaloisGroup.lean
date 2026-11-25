-- Prove2me | solution 1 for FiniteField.artinSchreier_translate_invariants_algEquiv_and_isGaloisGroup
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:30:24.007898+00:00
-- url     : https://prove2.me/submissions/e01ca40b-05ad-43a4-9d2d-12fa74419f3b

import Mathlib

/-!
# Invariants of `F_q[X]` under translations (Artin-Schreier cover of the affine line)

`F_q` acts on `F_q[X]` by translations `p ↦ p(X + c)`. The invariant ring is the polynomial ring in
`T = X^q - X`: `g ↦ g(X^q - X)` is an `F_q`-algebra isomorphism `F_q[T] ≃ F_q[X]^{F_q}`. Moreover
`F_q[X]` over the invariants is a finite Galois extension of rings with group `(F_q, +)` in which
every prime has trivial inertia (`σ • X - X = c` is a unit for `c ≠ 0`).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.K0Sol

section Poly

variable (Fq : Type) [Field Fq] [Fintype Fq]

theorem add_pow_card (a b : Fq[X]) :
    (a + b) ^ Fintype.card Fq = a ^ Fintype.card Fq + b ^ Fintype.card Fq := by
  have hF : ∀ x : Fq[X], FiniteField.frobeniusAlgHom Fq Fq[X] x = x ^ Fintype.card Fq := fun _ => rfl
  rw [← hF, map_add, hF, hF]

theorem one_lt_card : 1 < Fintype.card Fq := Fintype.one_lt_card

/-- The Artin-Schreier polynomial `X^q - X`. -/
noncomputable def asP : Fq[X] := X ^ Fintype.card Fq - X

theorem asP_natDegree : (asP Fq).natDegree = Fintype.card Fq :=
  FiniteField.X_pow_card_sub_X_natDegree_eq Fq (one_lt_card Fq)

theorem asP_ne_zero : asP Fq ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero Fq (one_lt_card Fq)

theorem asP_monic : (asP Fq).Monic :=
  monic_X_pow_sub (by rw [degree_X]; exact_mod_cast one_lt_card Fq)

theorem asP_comp (c : Fq) : (asP Fq).comp (X + C c) = asP Fq := by
  rw [asP, sub_comp, pow_comp, X_comp, add_pow_card, ← C_pow, FiniteField.pow_card]
  ring

theorem asP_dvd {r : Fq[X]} (h : ∀ c : Fq, r.eval c = 0) : asP Fq ∣ r := by
  by_cases hr : r = 0
  · rw [hr]; exact dvd_zero _
  have hroots : (asP Fq).roots ≤ r.roots := by
    rw [asP, FiniteField.roots_X_pow_card_sub_X Fq]
    exact (Multiset.le_iff_subset Finset.univ.nodup).2 fun c _ => (mem_roots hr).2 (h c)
  have hcard : Multiset.card (asP Fq).roots = (asP Fq).natDegree := by
    rw [asP_natDegree, asP, FiniteField.roots_X_pow_card_sub_X Fq]
    rfl
  have hd := (Multiset.prod_X_sub_C_dvd_iff_le_roots hr _).2 hroots
  rwa [prod_multiset_X_sub_C_of_monic_of_roots_card_eq (asP_monic Fq) hcard] at hd

theorem eval_eq_of_inv {p : Fq[X]} (hp : ∀ c : Fq, p.comp (X + C c) = p) (c : Fq) :
    p.eval c = p.eval 0 := by
  have h := congrArg (eval 0) (hp c)
  rw [eval_comp] at h
  simpa using h

/-- Every translation-invariant polynomial is a polynomial in `X^q - X`. -/
theorem exists_comp_of_inv : ∀ (n : ℕ) (p : Fq[X]), p.natDegree = n →
    (∀ c : Fq, p.comp (X + C c) = p) → ∃ g : Fq[X], p = g.comp (asP Fq) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp
  obtain ⟨s, hs⟩ := asP_dvd Fq (r := p - C (p.eval 0)) fun c => by
    rw [eval_sub, eval_C, eval_eq_of_inv Fq hp c, sub_self]
  by_cases hs0 : s = 0
  · refine ⟨C (p.eval 0), ?_⟩
    rw [C_comp]
    rw [hs0, mul_zero, sub_eq_zero] at hs
    exact hs
  have hsm : ∀ c : Fq, s.comp (X + C c) = s := by
    intro c
    have h1 : (p - C (p.eval 0)).comp (X + C c) = p - C (p.eval 0) := by
      rw [sub_comp, hp c, C_comp]
    rw [hs, mul_comp, asP_comp] at h1
    exact mul_left_cancel₀ (asP_ne_zero Fq) h1
  have hlt : s.natDegree < n := by
    have h1 : (p - C (p.eval 0)).natDegree = Fintype.card Fq + s.natDegree := by
      rw [hs, natDegree_mul (asP_ne_zero Fq) hs0, asP_natDegree]
    rw [natDegree_sub_C] at h1
    have := one_lt_card Fq
    omega
  obtain ⟨g, hg⟩ := ih _ hlt s rfl hsm
  refine ⟨C (p.eval 0) + X * g, ?_⟩
  rw [add_comp, mul_comp, C_comp, X_comp, ← hg, ← hs]
  ring

theorem comp_asP_injective : Function.Injective fun g : Fq[X] => g.comp (asP Fq) := by
  refine (injective_iff_map_eq_zero' (compRingHom (asP Fq))).2 fun g => ⟨fun h => ?_, fun h => ?_⟩
  · change g.comp (asP Fq) = 0 at h
    rcases comp_eq_zero_iff.1 h with h0 | ⟨_, hC⟩
    · exact h0
    · have h2 := congrArg natDegree hC
      rw [natDegree_C, asP_natDegree] at h2
      exact absurd h2 (by have := one_lt_card Fq; omega)
  · rw [h, map_zero]

end Poly

section Act

variable (Fq : Type) [Field Fq] [Fintype Fq]
  [MulSemiringAction (Multiplicative Fq) Fq[X]] [SMulCommClass (Multiplicative Fq) Fq Fq[X]]

theorem mem_fix_iff
    (hact : ∀ (c : Multiplicative Fq) (p : Fq[X]), c • p = p.comp (X + C (Multiplicative.toAdd c)))
    (p : Fq[X]) :
    p ∈ FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq) ↔ ∀ c : Fq, p.comp (X + C c) = p := by
  change (∀ c : Multiplicative Fq, c • p = p) ↔ _
  constructor
  · intro h c
    have h1 := h (Multiplicative.ofAdd c)
    rwa [hact, toAdd_ofAdd] at h1
  · intro h c
    rw [hact]
    exact h _

theorem main
    (hact : ∀ (c : Multiplicative Fq) (p : Fq[X]), c • p = p.comp (X + C (Multiplicative.toAdd c))) :
    (∃ e : Fq[X] ≃ₐ[Fq] FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq),
      ∀ g : Fq[X], (e g : Fq[X]) = g.comp (X ^ Fintype.card Fq - X)) ∧
    IsGaloisGroup (Multiplicative Fq) (FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq)) Fq[X] ∧
    Module.Finite (FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq)) Fq[X] ∧
    ∀ Q : Ideal Fq[X], Q.IsPrime → Q.inertia (Multiplicative Fq) = ⊥ := by
  have hmem : asP Fq ∈ FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq) :=
    (mem_fix_iff Fq hact _).2 (asP_comp Fq)
  set T : FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq) := ⟨asP Fq, hmem⟩ with hT
  have hcoe : ∀ g : Fq[X],
      ((aeval T g : FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq)) : Fq[X]) = g.comp (asP Fq) := by
    intro g
    rw [aeval_subalgebra_coe, comp_eq_aeval]
  have hbij : Function.Bijective (aeval T : Fq[X] →ₐ[Fq] _) := by
    refine ⟨fun g h hgh => comp_asP_injective Fq ?_, fun p => ?_⟩
    · have := congrArg Subtype.val hgh
      simpa only [hcoe] using this
    · obtain ⟨g, hg⟩ := exists_comp_of_inv Fq _ p.1 rfl ((mem_fix_iff Fq hact _).1 p.2)
      exact ⟨g, Subtype.ext (by rw [hcoe, ← hg])⟩
  have hgal : IsGaloisGroup (Multiplicative Fq) (FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq))
      Fq[X] :=
    { faithful := ⟨fun {a b} h => by
        have h1 := h X
        rw [hact, hact, X_comp, X_comp, add_right_inj, C_inj] at h1
        exact Multiplicative.toAdd.injective h1⟩
      commutes := inferInstance
      isInvariant := ⟨fun x h => ⟨⟨x, h⟩, rfl⟩⟩ }
  refine ⟨⟨AlgEquiv.ofBijective _ hbij, fun g => hcoe g⟩, hgal, ?_, ?_⟩
  · have : Algebra.IsIntegral (FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq)) Fq[X] :=
      Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq)) Fq[X]
        (Multiplicative Fq)
    have : Algebra.FiniteType (FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq)) Fq[X] :=
      Algebra.FiniteType.of_restrictScalars_finiteType Fq
        (FixedPoints.subalgebra Fq Fq[X] (Multiplicative Fq)) Fq[X]
    exact Algebra.IsIntegral.finite
  · intro Q hQ
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    have h : σ • (X : Fq[X]) - X ∈ Q := hσ X
    rw [hact, X_comp, add_sub_cancel_left] at h
    by_contra hne
    have hc : Multiplicative.toAdd σ ≠ 0 := fun h0 => hne (toAdd_eq_zero.1 h0)
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q h (isUnit_C.2 (Ne.isUnit hc)))

end Act

end RamanujanPetersson.K0Sol

theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq]
    [MulSemiringAction (Multiplicative Fq) (Polynomial Fq)]
    [SMulCommClass (Multiplicative Fq) Fq (Polynomial Fq)]
    (hact : ∀ (c : Multiplicative Fq) (p : Polynomial Fq),
      c • p = p.comp (Polynomial.X + Polynomial.C (Multiplicative.toAdd c))) :
    (∃ e : Polynomial Fq ≃ₐ[Fq] FixedPoints.subalgebra Fq (Polynomial Fq) (Multiplicative Fq),
      ∀ g : Polynomial Fq,
        (e g : Polynomial Fq) = g.comp (Polynomial.X ^ Fintype.card Fq - Polynomial.X)) ∧
    IsGaloisGroup (Multiplicative Fq) (FixedPoints.subalgebra Fq (Polynomial Fq) (Multiplicative Fq))
      (Polynomial Fq) ∧
    Module.Finite (FixedPoints.subalgebra Fq (Polynomial Fq) (Multiplicative Fq)) (Polynomial Fq) ∧
    ∀ Q : Ideal (Polynomial Fq), Q.IsPrime → Q.inertia (Multiplicative Fq) = ⊥ := by
  exact RamanujanPetersson.K0Sol.main Fq hact
