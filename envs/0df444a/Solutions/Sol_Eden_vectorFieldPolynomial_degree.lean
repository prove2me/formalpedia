-- Prove2me | solution 1 for Eden.vectorFieldPolynomial_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:07.026002+00:00
-- url     : https://prove2.me/submissions/922a60ea-2115-4e77-9178-2d4242c24f72

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
import Theorems.Thm_Eden_totalDegree_vectorFieldPolynomial_le
import Theorems.Thm_Eden_totalDegree_vectorFieldPolynomial_first

set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial
namespace Eden
theorem _root_.solution (c : ℝ) :
    Finset.univ.sup (fun i => (vectorFieldPolynomial c i).totalDegree) = 5 := by
  apply le_antisymm
  · exact Finset.sup_le (fun i _ => totalDegree_vectorFieldPolynomial_le c i)
  · simpa only [totalDegree_vectorFieldPolynomial_first] using
      (Finset.le_sup (f := fun i => (vectorFieldPolynomial c i).totalDegree)
        (Finset.mem_univ (0 : Fin 5)))
end Eden
