-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1_master_of_geometricRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:27.702655+00:00
-- url     : https://prove2.me/submissions/18ad7979-dd9b-494e-8eab-35a7b91410d1

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1_master
import Theorems.Thm_FourierJacobi_Analysis_i1_basic_nonzero

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
    (hd : d ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1)
      (∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩) := by
  obtain ⟨ht,hq0,hq1⟩ := i1_basic_nonzero q t hqt h.t2
  exact hasSum_i1_master q t d U V T ht hd hq0 hq1 hqt h
end FourierJacobi.Analysis
