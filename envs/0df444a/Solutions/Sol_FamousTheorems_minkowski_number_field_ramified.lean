-- Prove2me | solution 1 for FamousTheorems.minkowski_number_field_ramified
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:21:48.794211+00:00
-- url     : https://prove2.me/submissions/71ed0d4b-6ef6-44b2-b5d4-239b13c3329d

import Mathlib

theorem solution {K : Type*} [Field K] [NumberField K] (h : Module.finrank ℚ K ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ¬Algebra.IsUnramifiedIn (NumberField.RingOfIntegers K) (Ideal.span {(p : ℤ)}) :=
  NumberField.exists_not_isUnramifiedIn h
