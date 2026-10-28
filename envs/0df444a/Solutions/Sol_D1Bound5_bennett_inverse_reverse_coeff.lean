-- Prove2me | solution 1 for D1Bound5.bennett_inverse_reverse_coeff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:02.643439+00:00
-- url     : https://prove2.me/submissions/6f9e9bed-111e-496f-aaec-64bbe03362f3

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
open Finset Polynomial

namespace D1Bound5

section Reverse

variable {F : Type*} [Field F]

/-- For a monic polynomial of positive degree, coefficients of its reciprocal
at infinity are the top coefficients of monomial remainders. The proof uses
polynomial reflection, so it introduces no analytic convergence assumption. -/
theorem _root_.solution
    (D : F[X]) (hD : D.Monic) (hd : 0 < D.natDegree)
    (H : PowerSeries F) (hH : (D.reverse : PowerSeries F) * H = 1) (t : ℕ) :
    PowerSeries.coeff t H =
      ((X ^ (D.natDegree - 1 + t)) %ₘ D).coeff (D.natDegree - 1) := by
  classical
  let d := D.natDegree
  let f : F[X] := X ^ (d - 1 + t)
  let r := f %ₘ D
  let q := f /ₘ D
  have hd' : 0 < d := hd
  have hq : q.natDegree ≤ t := by
    dsimp [q, f]
    rw [Polynomial.natDegree_divByMonic _ hD, Polynomial.natDegree_X_pow]
    dsimp [d]
    omega
  have hr : r.degree < (d : ℕ) := by
    have h := Polynomial.degree_modByMonic_lt f hD
    simpa only [Polynomial.degree_eq_natDegree hD.ne_zero] using h
  have hH0 : PowerSeries.coeff 0 H = 1 := by
    have h := congrArg PowerSeries.constantCoeff hH
    simp only [map_mul, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse,
      show D.leadingCoeff = 1 from hD, map_one, one_mul] at h
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h
  have hreflect :
      r.reflect (d + t) + D.reverse * q.reflect t = X := by
    calc
      _ = (r + D * q).reflect (d + t) := by
        rw [Polynomial.reflect_add, Polynomial.reflect_mul D q le_rfl hq]
        rfl
      _ = f.reflect (d + t) :=
        congrArg (Polynomial.reflect (d + t)) (Polynomial.modByMonic_add_div f D)
      _ = X := by
        dsimp [f]
        rw [Polynomial.reflect_monomial, Polynomial.revAt_le (by omega)]
        have he : d + t - (d - 1 + t) = 1 := by omega
        rw [he, pow_one]
  have hqzero : (q.reflect t).coeff (t + 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact (Polynomial.natDegree_reflect_le.trans (max_le le_rfl hq)).trans_lt
      (Nat.lt_succ_self t)
  have hrzero (i : ℕ) (hi : i < t + 1) :
      (r.reflect (d + t)).coeff i = 0 := by
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by omega)]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    have hidx : d ≤ d + t - i := by omega
    exact hr.trans_le (WithBot.coe_le_coe.mpr hidx)
  have hrfirst : (r.reflect (d + t)).coeff (t + 1) = r.coeff (d - 1) := by
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by omega)]
    congr 1
    omega
  have hproduct : PowerSeries.coeff (t + 1)
      ((r.reflect (d + t) : PowerSeries F) * H) = r.coeff (d - 1) := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (t + 1, 0)]
    · rw [Polynomial.coeff_coe, hrfirst, hH0, mul_one]
    · rintro ⟨i, j⟩ hij hne
      have hij' := Finset.mem_antidiagonal.mp hij
      have hi : i < t + 1 := by
        by_contra hh
        have he : i = t + 1 ∧ j = 0 := by omega
        exact hne (Prod.ext he.1 he.2)
      rw [Polynomial.coeff_coe, hrzero i hi, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_antidiagonal.mpr (by omega))).elim
  have hs := congrArg (fun p : F[X] => (p : PowerSeries F) * H) hreflect
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, add_mul] at hs
  have hreorder : (D.reverse : PowerSeries F) * (q.reflect t : PowerSeries F) * H =
      (q.reflect t : PowerSeries F) * ((D.reverse : PowerSeries F) * H) := by ring
  rw [hreorder, hH, mul_one] at hs
  have hc := congrArg (PowerSeries.coeff (t + 1)) hs
  rw [map_add, hproduct, Polynomial.coeff_coe, hqzero, add_zero] at hc
  have hX : PowerSeries.coeff (t + 1) (PowerSeries.X * H) =
      PowerSeries.coeff t H := by
    simpa only [pow_one] using PowerSeries.coeff_X_pow_mul H 1 t
  exact (hc.trans hX).symm

end Reverse

section Residues

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]

















end Residues

end D1Bound5
end
