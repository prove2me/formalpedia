-- Prove2me | solution 1 for FiniteField.artinSchreier_isFrobenius_translate_iff_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T05:49:41.595486+00:00
-- url     : https://prove2.me/submissions/a62df6be-83c7-4a78-b8a2-1b0d4ad9fa05

import Mathlib

set_option autoImplicit false

namespace ASTraceFrob

open Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq]

theorem pow_card_pow_eq_expand (j : ℕ) (g : Fq[X]) :
    g ^ (Fintype.card Fq ^ j) = expand Fq (Fintype.card Fq ^ j) g := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, ← FiniteField.expand_card, expand_expand, mul_comm]

theorem X_pow_card_pow_sub_X (d : ℕ) :
    (X : Fq[X]) ^ (Fintype.card Fq ^ d) - X =
      ∑ j ∈ Finset.range d, (X ^ Fintype.card Fq - X) ^ (Fintype.card Fq ^ j) := by
  have h : ∀ j, (X ^ Fintype.card Fq - X : Fq[X]) ^ (Fintype.card Fq ^ j) =
      X ^ (Fintype.card Fq ^ (j + 1)) - X ^ (Fintype.card Fq ^ j) := by
    intro j
    rw [pow_card_pow_eq_expand, map_sub, map_pow, expand_X, ← pow_mul, ← pow_succ]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih, h]
    ring

end ASTraceFrob

open Polynomial in
theorem solution
    (Fq : Type*) [Field Fq] [Fintype Fq]
    (P : Ideal (Polynomial Fq)) [P.IsMaximal] (Q : Ideal (Polynomial Fq))
    (hQ : Q.comap (Polynomial.aeval (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq)) = P)
    (c : Fq) :
    (∀ f : Polynomial Fq,
        f.comp (Polynomial.X + Polynomial.C c) - f ^ Nat.card (Polynomial Fq ⧸ P) ∈ Q) ↔
      c = Algebra.trace Fq (Polynomial Fq ⧸ P) (Ideal.Quotient.mk P Polynomial.X) := by
  let _ : Field (Fq[X] ⧸ P) := Ideal.Quotient.field P
  have : Algebra.FiniteType Fq (Fq[X] ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ Fq P) (Ideal.Quotient.mkₐ_surjective Fq P)
  have : Module.Finite Fq (Fq[X] ⧸ P) := finite_of_finite_type_of_isJacobsonRing Fq _
  have : Finite (Fq[X] ⧸ P) := Module.finite_of_finite Fq
  have hN : Nat.card (Fq[X] ⧸ P) = Fintype.card Fq ^ Module.finrank Fq (Fq[X] ⧸ P) := by
    rw [Module.natCard_eq_pow_finrank (K := Fq), Nat.card_eq_fintype_card]
  -- the trace as a sum of conjugates, pulled back to the base
  have hsP : (∑ j ∈ Finset.range (Module.finrank Fq (Fq[X] ⧸ P)), (X : Fq[X]) ^ (Fintype.card Fq ^ j) -
      C (Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X))) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
    have htr := FiniteField.algebraMap_trace_eq_sum_pow Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X)
    rw [Nat.card_eq_fintype_card] at htr
    have hC : Ideal.Quotient.mk P (C (Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X))) =
        algebraMap Fq (Fq[X] ⧸ P) (Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X)) :=
      rfl
    simp only [map_pow]
    rw [hC, htr, sub_self]
  -- key congruence: X ^ N ≡ X + Tr(T mod P) mod Q
  have hkey : (X : Fq[X]) ^ Nat.card (Fq[X] ⧸ P) - X -
      C (Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X)) ∈ Q := by
    have h1 := Ideal.mem_comap.1 (hQ.ge hsP)
    rw [map_sub, map_sum, aeval_C, Polynomial.algebraMap_eq] at h1
    simp only [map_pow, aeval_X] at h1
    rw [hN, ASTraceFrob.X_pow_card_pow_sub_X]
    exact h1
  constructor
  · intro h
    have h1 := h X
    rw [X_comp] at h1
    have h2 := Q.add_mem h1 hkey
    have h3 : (X + C c - X ^ Nat.card (Fq[X] ⧸ P)) + (X ^ Nat.card (Fq[X] ⧸ P) - X -
        C (Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X))) =
        C (c - Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X)) := by
      rw [C_sub]; ring
    rw [h3] at h2
    by_contra hne
    have hu : IsUnit (C (c - Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X))) :=
      isUnit_C.2 (sub_ne_zero.2 hne).isUnit
    have hQt : Q = ⊤ := Ideal.eq_top_of_isUnit_mem Q h2 hu
    have hPt : P = ⊤ := by rw [← hQ, hQt, Ideal.comap_top]
    exact (Ideal.IsMaximal.ne_top inferInstance) hPt
  · intro hc f
    subst hc
    have hmem : (X + C (Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X))) -
        X ^ Nat.card (Fq[X] ⧸ P) ∈ Q := by
      have := Q.neg_mem hkey
      have e : -(X ^ Nat.card (Fq[X] ⧸ P) - X - C (Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X))) =
          (X + C (Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X))) - X ^ Nat.card (Fq[X] ⧸ P) := by ring
      rwa [e] at this
    have hpow : f ^ Nat.card (Fq[X] ⧸ P) = f.comp (X ^ Nat.card (Fq[X] ⧸ P)) := by
      rw [hN, ASTraceFrob.pow_card_pow_eq_expand, expand_eq_comp_X_pow]
    rw [hpow]
    have hdvd := sub_dvd_eval_sub (X + C (Algebra.trace Fq (Fq[X] ⧸ P) (Ideal.Quotient.mk P X)))
      (X ^ Nat.card (Fq[X] ⧸ P)) (f.map C)
    rw [eval_map, eval_map] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    show f.eval₂ C _ - f.eval₂ C _ ∈ Q
    rw [hk]
    exact Q.mul_mem_right k hmem
