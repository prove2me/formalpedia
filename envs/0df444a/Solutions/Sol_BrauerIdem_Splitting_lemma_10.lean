-- Prove2me | solution 1 for BrauerIdem.Splitting.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:58:36.327439+00:00
-- url     : https://prove2.me/submissions/f9868467-8bc0-417a-8770-342a278228db

import Mathlib

theorem solution {Λ : Type*} [Ring Λ] (J : TwoSidedIdeal Λ) :
    (∃ s : J.ringCon.Quotient →+ Λ,
      (∀ x, J.ringCon.mk' (s x) = x) ∧
      (∀ (a b : Λ) (x : J.ringCon.Quotient),
        s (J.ringCon.mk' a * x * J.ringCon.mk' b) = a * s x * b)) ↔
    (∃ φ : Λ, φ - 1 ∈ J ∧
      (∀ j ∈ J, φ * j = 0 ∧ j * φ = 0) ∧
      (∀ ψ : Λ, ψ - 1 ∈ J → (∀ j ∈ J, ψ * j = 0 ∧ j * ψ = 0) → ψ = φ) ∧
      φ * φ = φ ∧ (∀ a : Λ, φ * a = a * φ)) := by
  set mk := J.ringCon.mk' with hmk
  have key : ∀ a : Λ, mk a = 0 ↔ a ∈ J := by
    intro a
    rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
    rfl
  have keq : ∀ a b : Λ, mk a = mk b ↔ a - b ∈ J := by
    intro a b
    rw [← key, map_sub, sub_eq_zero]
  -- uniqueness helper
  have uniq : ∀ φ ψ : Λ, φ - 1 ∈ J → (∀ j ∈ J, φ * j = 0 ∧ j * φ = 0) →
      ψ - 1 ∈ J → (∀ j ∈ J, ψ * j = 0 ∧ j * ψ = 0) → ψ = φ := by
    intro φ ψ hφ hφJ hψ hψJ
    have h1 : ψ * (φ - 1) = 0 := (hψJ _ hφ).1
    have h2 : (ψ - 1) * φ = 0 := (hφJ _ hψ).2
    rw [mul_sub, mul_one, sub_eq_zero] at h1
    rw [sub_mul, one_mul, sub_eq_zero] at h2
    rw [← h1, h2]
  constructor
  · rintro ⟨s, hs1, hs2⟩
    have hφJ : ∀ j ∈ J, s 1 * j = 0 ∧ j * s 1 = 0 := by
      intro j hj
      have hj0 : mk j = 0 := (key j).mpr hj
      constructor
      · have := hs2 1 j 1
        rw [hj0, mul_zero, map_zero, one_mul] at this
        exact this.symm
      · have := hs2 j 1 1
        rw [hj0, zero_mul, zero_mul, map_zero, mul_one] at this
        exact this.symm
    have hφ1 : s 1 - 1 ∈ J := by
      rw [← key, map_sub, hs1, map_one, sub_self]
    refine ⟨s 1, hφ1, hφJ, fun ψ hψ hψJ => uniq _ _ hφ1 hφJ hψ hψJ, ?_, ?_⟩
    · have := (hφJ _ hφ1).1
      rw [mul_sub, mul_one, sub_eq_zero] at this
      exact this
    · intro a
      have e1 := hs2 1 a 1
      have e2 := hs2 a 1 1
      simp only [map_one, one_mul, mul_one] at e1 e2
      rw [← e1, ← e2]
  · rintro ⟨φ, hφ1, hφJ, -, -, hcen⟩
    have hφeq : ∀ a b : Λ, mk a = mk b → φ * a = φ * b := by
      intro a b h
      have := (hφJ _ ((keq a b).mp h)).1
      rw [mul_sub, sub_eq_zero] at this
      exact this
    have hsurj : Function.Surjective mk := RingCon.mk'_surjective _
    set r := Function.surjInv hsurj with hrdef
    have hr : ∀ x, mk (r x) = x := Function.surjInv_eq hsurj
    let s : J.ringCon.Quotient →+ Λ :=
      { toFun := fun x => φ * r x
        map_zero' := (hφJ _ ((key _).mp (hr 0))).1
        map_add' := fun x y => by
          rw [← mul_add]
          apply hφeq
          rw [map_add, hr, hr, hr] }
    have hmkφ : mk φ = 1 := by
      have := (keq φ 1).mpr hφ1
      rwa [map_one] at this
    refine ⟨s, fun x => ?_, fun a b x => ?_⟩
    · show mk (φ * r x) = x
      rw [map_mul, hmkφ, one_mul, hr]
    · show φ * r (mk a * x * mk b) = a * (φ * r x) * b
      have : φ * r (mk a * x * mk b) = φ * (a * r x * b) := by
        apply hφeq
        rw [hr, map_mul, map_mul, hr]
      rw [this, ← mul_assoc, ← mul_assoc, hcen, mul_assoc a φ]
