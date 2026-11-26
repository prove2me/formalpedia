-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i1_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:06.234419+00:00
-- url     : https://prove2.me/submissions/654eac45-a414-4de5-bfc9-984198ae848d

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1_cell

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
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : LatticeIndex => ‖masterTerm q t d U V T 1 p‖) := by
  apply i1PartitionEquiv.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun p => norm_nonneg _)).mpr
  exact ⟨summable_norm_i1_cell q t d U V T ht hqt h, (hasSum_fintype _).summable⟩
end FourierJacobi.Analysis
