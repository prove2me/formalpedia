-- Prove2me | solution 1 for D1Bound5.bennettTwoOtherPoles_two
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:00.651101+00:00
-- url     : https://prove2.me/submissions/9f5816a8-aeb6-4da8-855e-391f15136509

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]













theorem _root_.solution (a b : F) (k : ℕ) (i : Fin 3) :
    bennettOtherPoles Finset.univ (bennettTwoNodes a b) k i 2 =
      bennettPoleSeries a (k + if i = 0 then 1 else 0) *
        bennettPoleSeries (a - b) (k + if i = 1 then 1 else 0) := by
  have hs : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  simp [bennettOtherPoles, hs, bennettTwoNodes, Matrix.cons_val_two]















end D1Bound5
end
