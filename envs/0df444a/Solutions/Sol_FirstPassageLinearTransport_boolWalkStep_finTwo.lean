-- Prove2me | solution 1 for FirstPassageLinearTransport.boolWalkStep_finTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:12.526843+00:00
-- url     : https://prove2.me/submissions/8811b6f5-ced4-4477-a53a-3032e4607a68

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution (b : Fin 2) :
    boolWalkStep (finTwoEquiv b) = 2 * (b : ℤ) - 1 := by
  fin_cases b <;> norm_num [boolWalkStep, finTwoEquiv]
end FirstPassageLinearTransport
