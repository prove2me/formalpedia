-- Prove2me | solution 1 for BookProof.ChapterH1.resolvent_identity
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:31:07.98412+00:00
-- url     : https://prove2.me/submissions/1cc4457f-872c-4a06-8453-16109221eab2

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NoncommRing
set_option autoImplicit false
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem solution (a : A) (gj gm : ℂ) (Xj Xm : A)
    (_hjl : (algebraMap ℂ A gj - a) * Xj = 1) (hjr : Xj * (algebraMap ℂ A gj - a) = 1)
    (hml : (algebraMap ℂ A gm - a) * Xm = 1) (_hmr : Xm * (algebraMap ℂ A gm - a) = 1) :
    Xj - Xm = (gm - gj) • (Xj * Xm) := by
  calc
    Xj - Xm = Xj * ((algebraMap ℂ A gm - a) * Xm) -
        (Xj * (algebraMap ℂ A gj - a)) * Xm := by rw [hml, hjr, mul_one, one_mul]
    _ = (Xj * algebraMap ℂ A (gm - gj)) * Xm := by rw [map_sub]; noncomm_ring
    _ = (gm - gj) • (Xj * Xm) := by
      rw [Algebra.smul_def, ← (Algebra.commutes (gm - gj) Xj), mul_assoc]
#print axioms solution
