-- Prove2me | solution 1 for D1Bound5.clearedPoleNumerator_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:24:59.743412+00:00
-- url     : https://prove2.me/submissions/2ae02004-a0b3-4c77-ab7b-f9be417ca3ca

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions

section
open Finset Polynomial

namespace D1Bound5

section CommRing

variable {R ι : Type*} [CommRing R] [Nontrivial R]
variable [Fintype ι] [DecidableEq ι]





theorem _root_.solution (a : ι → R) (e : ι → ℕ)
    (i : ι) (j : Fin (e i + 1)) :
    (clearedPoleNumerator a e i j).natDegree =
      j.val + ∑ l ∈ (Finset.univ : Finset ι).erase i, (e l + 1) := by
  unfold clearedPoleNumerator
  rw [((Polynomial.monic_X_sub_C (a i)).pow j.val).natDegree_mul
    (Polynomial.monic_prod_of_monic _ _ fun l _ ↦
      (Polynomial.monic_X_sub_C (a l)).pow (e l + 1))]
  rw [Polynomial.natDegree_prod_of_monic
    (h := fun l _ ↦ (Polynomial.monic_X_sub_C (a l)).pow (e l + 1))]
  rw [(Polynomial.monic_X_sub_C (a i)).natDegree_pow,
    Polynomial.natDegree_X_sub_C, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [(Polynomial.monic_X_sub_C (a l)).natDegree_pow,
    Polynomial.natDegree_X_sub_C, mul_one]







end CommRing

end D1Bound5
end
