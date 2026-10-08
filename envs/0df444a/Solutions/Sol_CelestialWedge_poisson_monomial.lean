-- Prove2me | solution 1 for CelestialWedge.poisson_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:21:20.602158+00:00
-- url     : https://prove2.me/submissions/7f4ae9e3-b148-46cf-baf5-52cc227c1f85

import Mathlib
import Definitions.Def_celestial_wedge_algebra

open MvPolynomial in
theorem b35848c2_core (a b c d : ℕ) :
    pderiv 0 ((X 0 : MvPolynomial (Fin 2) ℂ) ^ a * X 1 ^ b) * pderiv 1 (X 0 ^ c * X 1 ^ d)
      - pderiv 1 ((X 0 : MvPolynomial (Fin 2) ℂ) ^ a * X 1 ^ b) * pderiv 0 (X 0 ^ c * X 1 ^ d)
      = ((a : ℂ) * d - b * c) • (X 0 ^ (a + c - 1) * X 1 ^ (b + d - 1)) := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, pderiv_X, Pi.single_apply,
    smul_eq_mul]
  simp
  rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;> rcases d with _ | d <;>
    simp [pow_succ, Algebra.smul_def] <;> ring

open CelestialWedge in
theorem solution (p m q n : ℚ) (hpm : InWedge p m) (hqn : InWedge q n) :
    poisson (monomialOf p m) (monomialOf q n) =
      (2 * ((structConst p m q n : ℚ) : ℂ)) • monomialOf (p + q - 2) (m + n) := by
  obtain ⟨a, b, ha, hb⟩ := hpm
  obtain ⟨c, d, hc, hd⟩ := hqn
  have e1 : (p + q - 2) + (m + n) - 1 = ((a + c : ℕ) : ℚ) - 1 := by push_cast; linarith
  have e2 : (p + q - 2) - (m + n) - 1 = ((b + d : ℕ) : ℚ) - 1 := by push_cast; linarith
  have hs : (2 * structConst p m q n : ℚ) = (a : ℚ) * d - b * c := by
    have hp : p = ((a : ℚ) + b + 2) / 2 := by linarith
    have hm : m = ((a : ℚ) - b) / 2 := by linarith
    have hq : q = ((c : ℚ) + d + 2) / 2 := by linarith
    have hn : n = ((c : ℚ) - d) / 2 := by linarith
    unfold structConst
    rw [hp, hm, hq, hn]
    ring
  have hs' : (2 * ((structConst p m q n : ℚ) : ℂ)) = (a : ℂ) * d - b * c := by
    have := congrArg (fun x : ℚ => (x : ℂ)) hs
    push_cast at this
    exact this
  rw [hs']
  unfold monomialOf poisson
  rw [ha, hb, hc, hd, e1, e2, Nat.floor_sub_one, Nat.floor_sub_one, Nat.floor_natCast,
    Nat.floor_natCast, Nat.floor_natCast, Nat.floor_natCast, Nat.floor_natCast, Nat.floor_natCast]
  exact b35848c2_core a b c d
