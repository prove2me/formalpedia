-- Prove2me | solution 1 for Eden.totalDegree_radiusPolynomial_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:25.063854+00:00
-- url     : https://prove2.me/submissions/5b8ef9fa-b3ce-4fa1-9157-dd021cd2aeec

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField

set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial
namespace Eden
theorem _root_.solution (i j : Fin 5) :
    (radiusPolynomial i j).totalDegree ≤ 2 := by
  exact (totalDegree_add _ _).trans (by simp)
end Eden
