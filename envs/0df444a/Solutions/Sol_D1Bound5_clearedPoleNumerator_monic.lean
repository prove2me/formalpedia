-- Prove2me | solution 1 for D1Bound5.clearedPoleNumerator_monic
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:19:59.215984+00:00
-- url     : https://prove2.me/submissions/88260ee1-564b-4059-95a7-d0ac0b3b797c

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
    (i : ι) (j : Fin (e i + 1)) : (clearedPoleNumerator a e i j).Monic := by
  apply Polynomial.Monic.mul ((Polynomial.monic_X_sub_C _).pow _)
  exact Polynomial.monic_prod_of_monic _ _ fun l _ ↦
    (Polynomial.monic_X_sub_C _).pow _









end CommRing

end D1Bound5
end
