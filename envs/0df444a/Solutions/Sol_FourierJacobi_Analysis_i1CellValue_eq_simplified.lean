-- Prove2me | solution 1 for FourierJacobi.Analysis.i1CellValue_eq_simplified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:51.785804+00:00
-- url     : https://prove2.me/submissions/ff9b8ab5-651b-476d-911b-2636932b60ac

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1r1_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r2_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r3ae_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r3ao_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r3b_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r3c_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r4_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r5_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r6a_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r6b_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r7_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r8ae_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r8ao_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r8b_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r8c_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r9_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r10_value_eq

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) (i : Fin 17) :
    i1CellValue q t d U V T i = i1CellSimplified t d U V T i := by
  fin_cases i
  · exact i1r1_value_eq q t d U V T ht hd hqt h
  · exact i1r2_value_eq q t d U V T ht hd hqt h
  · exact i1r3ae_value_eq q t d U V T ht hd hqt h
  · exact i1r3ao_value_eq q t d U V T ht hd hqt h
  · exact i1r3b_value_eq q t d U V T ht hd hqt h
  · exact i1r3c_value_eq q t d U V T ht hd hqt h
  · exact i1r4_value_eq q t d U V T ht hd hqt h
  · exact i1r5_value_eq q t d U V T ht hd hqt h
  · exact i1r6a_value_eq q t d U V T ht hd hqt h
  · exact i1r6b_value_eq q t d U V T ht hd hqt h
  · exact i1r7_value_eq q t d U V T ht hd hqt h
  · exact i1r8ae_value_eq q t d U V T ht hd hqt h
  · exact i1r8ao_value_eq q t d U V T ht hd hqt h
  · exact i1r8b_value_eq q t d U V T ht hd hqt h
  · exact i1r8c_value_eq q t d U V T ht hd hqt h
  · exact i1r9_value_eq q t d U V T ht hd hqt h
  · exact i1r10_value_eq q t d U V T ht hd hqt h
end FourierJacobi.Analysis
