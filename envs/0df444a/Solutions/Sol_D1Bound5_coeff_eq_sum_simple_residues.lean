-- Prove2me | solution 1 for D1Bound5.coeff_eq_sum_simple_residues
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:51.169292+00:00
-- url     : https://prove2.me/submissions/5d8ef3fc-01ac-4547-b7aa-9db0ea39c2d7

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
import Theorems.Thm_D1Bound5_clearedPoleNumerator_top_coeff

section
open Finset Polynomial

namespace D1Bound5

section CommRing

variable {R ι : Type*} [CommRing R] [Nontrivial R]
variable [Fintype ι] [DecidableEq ι]









/-- The coefficient one below the denominator degree is the sum of the
simple-pole coefficients in an exact cleared partial-fraction identity.
The identity itself is an explicit hypothesis, not inferred from notation. -/
theorem _root_.solution (a : ι → R) (e : ι → ℕ)
    (c : (i : ι) → Fin (e i + 1) → R) (f : R[X])
    (hdecomp : f = ∑ i, ∑ j : Fin (e i + 1),
      C (c i j) * clearedPoleNumerator a e i j) :
    f.coeff ((∑ l, (e l + 1)) - 1) = ∑ i, c i (Fin.last (e i)) := by
  classical
  rw [hdecomp, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, clearedPoleNumerator_top_coeff]
  simp



end CommRing

end D1Bound5
end
