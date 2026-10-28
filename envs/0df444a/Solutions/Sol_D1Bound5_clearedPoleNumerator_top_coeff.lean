-- Prove2me | solution 1 for D1Bound5.clearedPoleNumerator_top_coeff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:09.429003+00:00
-- url     : https://prove2.me/submissions/c2f0eadf-6461-4536-8a33-ac246c0b6044

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
import Theorems.Thm_D1Bound5_clearedPoleNumerator_monic
import Theorems.Thm_D1Bound5_clearedPoleNumerator_natDegree

section
open Finset Polynomial

namespace D1Bound5

section CommRing

variable {R ι : Type*} [CommRing R] [Nontrivial R]
variable [Fintype ι] [DecidableEq ι]







/-- At degree one below the denominator degree, only the cleared simple pole
has a nonzero coefficient. This calculation does not require distinct nodes. -/
theorem _root_.solution (a : ι → R) (e : ι → ℕ)
    (i : ι) (j : Fin (e i + 1)) :
    (clearedPoleNumerator a e i j).coeff ((∑ l, (e l + 1)) - 1) =
      if j = Fin.last (e i) then 1 else 0 := by
  have hsum : e i + 1 + ∑ l ∈ (Finset.univ : Finset ι).erase i, (e l + 1) =
      ∑ l, (e l + 1) :=
    Finset.add_sum_erase (Finset.univ : Finset ι) (fun l : ι ↦ e l + 1)
      (Finset.mem_univ i)
  split_ifs with hj
  · subst j
    have hd : (clearedPoleNumerator a e i (Fin.last (e i))).natDegree =
        (∑ l, (e l + 1)) - 1 := by
      rw [clearedPoleNumerator_natDegree, Fin.val_last]
      omega
    rw [← hd, Polynomial.coeff_natDegree]
    exact clearedPoleNumerator_monic a e i (Fin.last (e i))
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [clearedPoleNumerator_natDegree]
    have hlt := j.isLt
    have hne : j.val ≠ e i := by
      intro heq
      apply hj
      exact Fin.ext heq
    omega





end CommRing

end D1Bound5
end
