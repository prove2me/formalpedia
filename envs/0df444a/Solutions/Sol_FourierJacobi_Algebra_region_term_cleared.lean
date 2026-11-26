-- Prove2me | solution 1 for FourierJacobi.Algebra.region_term_cleared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:48.54102+00:00
-- url     : https://prove2.me/submissions/bdcba876-d087-46ae-a905-bab9a6691d0e

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Theorems.Thm_FourierJacobi_Algebra_regionCleared0
import Theorems.Thm_FourierJacobi_Algebra_regionCleared1
import Theorems.Thm_FourierJacobi_Algebra_regionCleared2
import Theorems.Thm_FourierJacobi_Algebra_regionCleared3
import Theorems.Thm_FourierJacobi_Algebra_regionCleared4
import Theorems.Thm_FourierJacobi_Algebra_regionCleared5
import Theorems.Thm_FourierJacobi_Algebra_regionCleared6
import Theorems.Thm_FourierJacobi_Algebra_regionCleared7
import Theorems.Thm_FourierJacobi_Algebra_regionCleared8
import Theorems.Thm_FourierJacobi_Algebra_regionCleared9
import Theorems.Thm_FourierJacobi_Algebra_regionCleared10
import Theorems.Thm_FourierJacobi_Algebra_regionCleared11
import Theorems.Thm_FourierJacobi_Algebra_regionCleared12
import Theorems.Thm_FourierJacobi_Algebra_regionCleared13
import Theorems.Thm_FourierJacobi_Algebra_regionCleared14
import Theorems.Thm_FourierJacobi_Algebra_regionCleared15
import Theorems.Thm_FourierJacobi_Algebra_regionCleared16
import Theorems.Thm_FourierJacobi_Algebra_regionCleared17
import Theorems.Thm_FourierJacobi_Algebra_regionCleared18
import Theorems.Thm_FourierJacobi_Algebra_regionCleared19
import Theorems.Thm_FourierJacobi_Algebra_regionCleared20
import Theorems.Thm_FourierJacobi_Algebra_regionCleared21
import Theorems.Thm_FourierJacobi_Algebra_regionCleared22
import Theorems.Thm_FourierJacobi_Algebra_regionCleared23
import Theorems.Thm_FourierJacobi_Algebra_regionCleared24
import Theorems.Thm_FourierJacobi_Algebra_regionCleared25
import Theorems.Thm_FourierJacobi_Algebra_regionCleared26
import Theorems.Thm_FourierJacobi_Algebra_regionCleared27
import Theorems.Thm_FourierJacobi_Algebra_regionCleared28
import Theorems.Thm_FourierJacobi_Algebra_regionCleared29
import Theorems.Thm_FourierJacobi_Algebra_regionCleared30
import Theorems.Thm_FourierJacobi_Algebra_regionCleared31
import Theorems.Thm_FourierJacobi_Algebra_regionCleared32
import Theorems.Thm_FourierJacobi_Algebra_regionCleared33
import Theorems.Thm_FourierJacobi_Algebra_regionCleared34
import Theorems.Thm_FourierJacobi_Algebra_regionCleared35
import Theorems.Thm_FourierJacobi_Algebra_regionCleared36
import Theorems.Thm_FourierJacobi_Algebra_regionCleared37
import Theorems.Thm_FourierJacobi_Algebra_regionCleared38
import Theorems.Thm_FourierJacobi_Algebra_regionCleared39
import Theorems.Thm_FourierJacobi_Algebra_regionCleared40
import Theorems.Thm_FourierJacobi_Algebra_regionCleared41
import Theorems.Thm_FourierJacobi_Algebra_regionCleared42
import Theorems.Thm_FourierJacobi_Algebra_regionCleared43
import Theorems.Thm_FourierJacobi_Algebra_regionCleared44
import Theorems.Thm_FourierJacobi_Algebra_regionCleared45
import Theorems.Thm_FourierJacobi_Algebra_regionCleared46
import Theorems.Thm_FourierJacobi_Algebra_regionCleared47
import Theorems.Thm_FourierJacobi_Algebra_regionCleared48
import Theorems.Thm_FourierJacobi_Algebra_regionCleared49

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
namespace FourierJacobi.Algebra
theorem _root_.solution (t d U V P N E F G : K)
    (hd : d ≠ 0) (hP : P ≠ 0) (hN : N ≠ 0) (hE : E ≠ 0)
    (hF : F ≠ 0) (hG : G ≠ 0) (i : Fin 50) :
    (d ^ 2 * P * N * E * F * G) * rawRegionTerms t d U V P N E F G i =
      rawRegionNumerators t d U V P N E F G i := by
  fin_cases i
  · exact regionCleared0 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared1 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared2 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared3 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared4 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared5 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared6 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared7 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared8 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared9 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared10 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared11 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared12 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared13 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared14 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared15 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared16 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared17 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared18 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared19 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared20 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared21 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared22 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared23 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared24 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared25 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared26 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared27 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared28 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared29 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared30 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared31 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared32 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared33 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared34 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared35 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared36 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared37 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared38 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared39 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared40 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared41 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared42 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared43 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared44 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared45 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared46 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared47 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared48 t d U V P N E F G hd hP hN hE hF hG
  · exact regionCleared49 t d U V P N E F G hd hP hN hE hF hG
end FourierJacobi.Algebra
