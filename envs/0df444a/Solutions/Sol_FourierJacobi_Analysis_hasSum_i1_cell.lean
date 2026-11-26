-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:30:59.813258+00:00
-- url     : https://prove2.me/submissions/59d9731f-f087-4fb3-8567-0702c6f9bcff

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r1_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r2_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r3ae_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r3ao_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r3b_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r3c_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r4_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r5_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r6a_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r6b_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r7_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r8ae_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r8ao_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r8b_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r8c_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r9_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r10_master

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
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) (i : Fin 17) :
    HasSum (fun p : I1Cell i => masterTerm q t d U V T 1 p.val)
      (i1CellValue q t d U V T i) := by
  fin_cases i
  · exact hasSum_i1r1_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r2_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3ae_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3ao_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3b_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3c_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r4_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r5_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r6a_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r6b_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r7_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8ae_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8ao_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8b_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8c_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r9_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r10_master q t d U V T ht hq0 hq1 hqt h
end FourierJacobi.Analysis
