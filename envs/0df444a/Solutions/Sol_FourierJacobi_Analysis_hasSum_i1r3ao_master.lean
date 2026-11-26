-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1r3ao_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:46.299409+00:00
-- url     : https://prove2.me/submissions/5ed14d18-f39c-41b1-b0da-63e468b79525

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1_qinv_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r3ao_master_reindexed
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r3ao_raw
import Theorems.Thm_FourierJacobi_Analysis_hasSum_weighted_collision
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1r3ao_raw


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
    HasSum (fun p : I1Cell 3 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r3ao_raw t d U V T 0 h.p h.e h.t2
  have hn := summable_norm_i1r3ao_raw t d U V T 0 h.p h.e h.t2
  apply i1r3aoDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R3AORow => p.val.2.1) (fun p : I1R3AORow => p.val.2.2)
    (fun p : I1R3AORow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r3ao_master_reindexed q t d U V T ht hqt p
end FourierJacobi.Analysis
