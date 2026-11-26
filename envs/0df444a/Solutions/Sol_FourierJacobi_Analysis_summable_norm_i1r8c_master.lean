-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i1r8c_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:28:58.884536+00:00
-- url     : https://prove2.me/submissions/ae465df4-8cdf-4ca6-bc5c-51b588e633b1

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1_qinv_eq
import Theorems.Thm_FourierJacobi_Analysis_i1_summable_norm_prob_tail
import Theorems.Thm_FourierJacobi_Analysis_i1r8c_master_reindexed
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1r8c_raw


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
    Summable (fun p : I1Cell 14 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r8c_raw t d U V T ht 1 (by omega) h.n h.e
  apply i1r8cDepthEquiv.summable_iff.mp
  convert hn.mul_norm (i1_summable_norm_prob_tail q hq) using 1
  exact funext fun p => congrArg norm (i1r8c_master_reindexed q t d U V T ht hqt p)
end FourierJacobi.Analysis
