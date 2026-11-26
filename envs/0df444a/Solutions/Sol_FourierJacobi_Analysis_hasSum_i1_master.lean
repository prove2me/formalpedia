-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:27.231088+00:00
-- url     : https://prove2.me/submissions/43f78000-5fa6-4493-a5b5-1b3e1cdaa88d

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1_master_cells
import Theorems.Thm_FourierJacobi_Analysis_i1CellValue_sum_eq_regions

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
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1)
      (∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩) := by
  rw [← i1CellValue_sum_eq_regions q t d U V T ht hd hqt h]
  exact hasSum_i1_master_cells q t d U V T ht hq0 hq1 hqt h
end FourierJacobi.Analysis
