-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1_master_cells
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:38.62331+00:00
-- url     : https://prove2.me/submissions/c6d6a558-c5e9-4805-8ce3-a03115107eef

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1_cell
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1_master

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
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1) (∑ i : Fin 17, i1CellValue q t d U V T i) := by
  have hs := (summable_norm_i1_master q t d U V T ht hqt h).of_norm
  apply i1PartitionEquiv.hasSum_iff.mp
  exact (hasSum_fintype (i1CellValue q t d U V T)).sigma_of_hasSum
    (hasSum_i1_cell q t d U V T ht hq0 hq1 hqt h)
    (i1PartitionEquiv.summable_iff.mpr hs)
end FourierJacobi.Analysis
