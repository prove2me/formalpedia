-- Prove2me | solution 1 for Eden.eval_vectorFieldPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:02.368241+00:00
-- url     : https://prove2.me/submissions/10aa0548-1571-49ad-a1f5-621548657a7a

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
theorem _root_.solution (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    eval (fun j => p j) (vectorFieldPolynomial c i) = vectorField c p i := by
  fin_cases i <;>
    simp [vectorFieldPolynomial, ratePolynomial, radiusPolynomial, vectorField,
      radiusSq₁, radiusSq₂, q]
end Eden
