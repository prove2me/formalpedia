-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r7_master_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:20.72605+00:00
-- url     : https://prove2.me/submissions/a6d87b64-6045-4513-a8f9-c826461e9943

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1Raw_eq_shell
import Theorems.Thm_FourierJacobi_Analysis_i1r7_cartan


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
theorem _root_.solution (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R7Row × ℕ) :
    masterTerm q t d U V T 1 (i1r7DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r7DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r7_cartan, i1r7_cartan]
    
  rw [he]
end FourierJacobi.Analysis
