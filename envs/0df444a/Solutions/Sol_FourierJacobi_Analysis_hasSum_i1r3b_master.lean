-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1r3b_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:27:21.854+00:00
-- url     : https://prove2.me/submissions/9ca4b67a-69bc-42c2-8db3-a81e84335a1a

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1_qinv_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r3b_master_reindexed
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r3b_raw
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1r3b_raw


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
    HasSum (fun p : I1Cell 4 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0)) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r3b_raw t d U V T h.p h.e
  have hn := summable_norm_i1r3b_raw t d U V T h.p h.e
  apply i1r3bDepthEquiv.hasSum_iff.mp
  convert hs.mul_right (collisionProbability q 0) using 1
  all_goals try rfl
  exact funext fun p => i1r3b_master_reindexed q t d U V T ht hqt p
end FourierJacobi.Analysis
