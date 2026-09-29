-- Prove2me | solution 2 for Diaz.real_quantisation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:20:59.789205+00:00
-- url     : https://prove2.me/submissions/8e5b0133-e1f2-491f-bf7c-14b532cfca40

/-
`Diaz.real_quantisation` is the `m = 1` case of `Diaz.order_quantisation`,
together with the quantisation of the imaginary part.  When `exp u` is real,
`exp u / conj (exp u) = 1`, so the order of that ratio divides `1`, and the
general bound `π²/m² < |u|²` becomes `π² < |u|²`.
-/
import Mathlib
import Theorems.Thm_Diaz_order_quantisation

open ComplexConjugate

theorem solution {u : ℂ} (hexp : (Complex.exp u).im = 0)
    (hre : u.re ≠ 0) (him : u.im ≠ 0) :
    (∃ n : ℤ, u.im = n * Real.pi) ∧ Real.pi ^ 2 < Complex.normSq u := by
  have hs : Real.sin u.im = 0 := by
    have hx := Complex.exp_im u
    rw [hexp] at hx
    rcases mul_eq_zero.mp hx.symm with h | h
    · exact absurd h (Real.exp_ne_zero _)
    · exact h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
  refine ⟨⟨n, hn.symm⟩, ?_⟩
  have hconj : conj (Complex.exp u) = Complex.exp u := by
    apply Complex.conj_eq_iff_im.mpr hexp
  have hξ : (Complex.exp u / conj (Complex.exp u)) ^ (1 : ℕ) = 1 := by
    rw [hconj, pow_one, div_self (Complex.exp_ne_zero u)]
  have key := Diaz.order_quantisation (m := 1) one_pos hξ hre him
  simpa using key
