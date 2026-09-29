-- Prove2me | solution 1 for FamousTheorems.cyclotomic_galois_group_units_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:33:04.415988+00:00
-- url     : https://prove2.me/submissions/2a52a22f-cd55-4cc7-a7f1-5c42b8eb78de

import Mathlib

theorem solution {n : ℕ} [NeZero n] {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {n} K L] (h : Irreducible (Polynomial.cyclotomic n K)) :
    Nonempty ((L ≃ₐ[K] L) ≃* (ZMod n)ˣ) :=
  ⟨IsCyclotomicExtension.autEquivPow L h⟩
