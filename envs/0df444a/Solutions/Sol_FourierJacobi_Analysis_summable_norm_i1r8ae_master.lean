-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i1r8ae_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:28:51.288851+00:00
-- url     : https://prove2.me/submissions/668035cf-3dd2-4f81-9042-1479bcb7af47

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1_qinv_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r8ae_master_reindexed
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1r8ae_raw
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_weighted_collision


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
    Summable (fun p : I1Cell 11 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r8ae_raw t d U V T 0 h.n h.e h.t2
  apply i1r8aeDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R8AERow => p.val.2.1) (fun p : I1R8AERow => p.val.2.2)
    (fun p : I1R8AERow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r8ae_master_reindexed q t d U V T ht hqt p)
end FourierJacobi.Analysis
