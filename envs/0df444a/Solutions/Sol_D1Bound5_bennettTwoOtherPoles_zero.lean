-- Prove2me | solution 1 for D1Bound5.bennettTwoOtherPoles_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T06:13:53.272231+00:00
-- url     : https://prove2.me/submissions/c0ca91c3-c34f-4ae8-bd51-8195a2e5ba61

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
    bennettOtherPoles Finset.univ (bennettTwoNodes a b) k i 0 =
      bennettPoleSeries (-b) (k + if i = 1 then 1 else 0) *
        bennettPoleSeries (-a) (k + if i = 2 then 1 else 0) := by
  have hs : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  simp [bennettOtherPoles, hs, bennettTwoNodes, Matrix.cons_val_two]



















end D1Bound5
end
