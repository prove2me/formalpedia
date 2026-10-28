-- Prove2me | solution 1 for D1Bound5.bennettPolynomialResidue_homogenize
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:57:05.042626+00:00
-- url     : https://prove2.me/submissions/f6203cbc-423f-4213-8273-1e1864006f0f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettResidueTaylor_homogenize

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]









section Nodes

variable {I : Type*} [DecidableEq I]





theorem _root_.solution (s : Finset I) (a : I → F)
    (k : ℕ) (ν N : F) (i j : I) (hN : N ≠ 0) :
    N ^ k * (bennettPolynomialResidue s a k ν i j).eval N⁻¹ =
      (bennettClearedResidue s a k ν i j).eval N := by
  apply bennettResidueTaylor_homogenize
  · split_ifs <;> omega
  · exact hN

end Nodes

end D1Bound5
end
