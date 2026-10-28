-- Prove2me | solution 1 for D1Bound5.exists_clearedPole_decomposition_zero_residue_sum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:11:57.440971+00:00
-- url     : https://prove2.me/submissions/56efa252-5dc3-4285-a635-421e3eb2153d

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
import Theorems.Thm_D1Bound5_coeff_eq_sum_simple_residues
import Theorems.Thm_D1Bound5_exists_clearedPole_decomposition

section
open Finset Polynomial

namespace D1Bound5

section CommRing

variable {R ι : Type*} [CommRing R] [Nontrivial R]
variable [Fintype ι] [DecidableEq ι]











/-- The algebraic residue sum vanishes when an exact cleared decomposition
has numerator degree at least two below the denominator degree. -/
theorem sum_simple_residues_eq_zero_of_degree_gap (a : ι → R) (e : ι → ℕ)
    (c : (i : ι) → Fin (e i + 1) → R) (f : R[X])
    (hdecomp : f = ∑ i, ∑ j : Fin (e i + 1),
      C (c i j) * clearedPoleNumerator a e i j)
    (hdeg : f.degree < ((∑ l, (e l + 1)) - 1 : ℕ)) :
    ∑ i, c i (Fin.last (e i)) = 0 := by
  rw [← coeff_eq_sum_simple_residues a e c f hdecomp]
  exact Polynomial.coeff_eq_zero_of_degree_lt hdeg

end CommRing

end D1Bound5
end

section
open Finset Polynomial

namespace D1Bound5

/-!
This module proves existence of the exact cleared partial-fraction decomposition
used by the residue-sum argument. The decomposition is a conclusion, not an
assumption. Identifying its coefficients with the manuscript's explicit finite
binomial sums remains a separate obligation.
-/

section CommRing

variable {R ι : Type*} [CommRing R] [Nontrivial R]
variable [Fintype ι] [DecidableEq ι]













end CommRing

section Field

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]



/-- Algebraic residue cancellation for an existing exact decomposition, now
obtained without any assumed decomposition identity. -/
theorem _root_.solution
    (a : ι → F) (ha : Function.Injective a) (e : ι → ℕ) (f : F[X])
    (hdeg : f.degree < ((∑ i, (e i + 1)) - 1 : ℕ)) :
    ∃ c : (i : ι) → Fin (e i + 1) → F,
      (f = ∑ i, ∑ j : Fin (e i + 1), C (c i j) * clearedPoleNumerator a e i j) ∧
      ∑ i, c i (Fin.last (e i)) = 0 := by
  obtain ⟨c, hc⟩ := exists_clearedPole_decomposition a ha e f
    (hdeg.trans_le (WithBot.coe_le_coe.mpr (Nat.sub_le _ _)))
  exact ⟨c, hc, sum_simple_residues_eq_zero_of_degree_gap a e c f hc hdeg⟩

end Field

end D1Bound5
end
