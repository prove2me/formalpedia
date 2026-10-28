-- Prove2me | solution 1 for D1Bound5.bennettClearedResidue_prefix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:11:56.435732+00:00
-- url     : https://prove2.me/submissions/f80d9674-4834-413d-86ca-0c3365b57778

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Theorems.Thm_D1Bound5_bennett_prod_erase_last_erase

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





/-- Removing the final node gives exactly the cleared residue construction on
the prefix, including the distinguished row multiplicity. -/
theorem _root_.solution (n : ℕ) (a : Fin (n + 1) → F)
    (k : ℕ) (ν : F) (i j : Fin n) :
    bennettClearedResidue (Finset.univ.erase (Fin.last n)) a k ν i.castSucc j.castSucc =
      bennettClearedResidue Finset.univ (fun l : Fin n ↦ a l.castSucc) k ν i j := by
  unfold bennettClearedResidue
  simp only [Fin.castSucc_inj]
  congr 1
  unfold bennettOtherPoles
  rw [bennett_prod_erase_last_erase]
  simp only [Fin.castSucc_inj]



end D1Bound5
end
