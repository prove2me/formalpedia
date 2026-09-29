-- Prove2me | solution 1 for BookProof.YangMillsHermite.RealCoeff.sum
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:55:09.267925+00:00
-- url     : https://prove2.me/submissions/f9ffcad8-535d-412c-8053-6acd8bdae40d

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false

theorem solution {d : ℕ} {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin d) ℂ}
    (h : ∀ i ∈ s, MvPolynomial.map (starRingEnd ℂ) (f i) = f i) :
    MvPolynomial.map (starRingEnd ℂ) (∑ i ∈ s, f i) = ∑ i ∈ s, f i := by
  rw [map_sum]
  exact Finset.sum_congr rfl h
#print axioms solution
