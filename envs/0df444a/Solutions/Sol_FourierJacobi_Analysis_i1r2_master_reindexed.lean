-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r2_master_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:44.725292+00:00
-- url     : https://prove2.me/submissions/63650132-9c24-41d1-be6a-c3de53375395

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1Raw_eq_shell
import Theorems.Thm_FourierJacobi_Analysis_i1r2_cartan


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
    (hqt : q*t^2=1) (p : I1R2Row × ℕ) :
    masterTerm q t d U V T 1 (i1r2DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r2DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r2_cartan, i1r2_cartan]
    
  rw [he]
end FourierJacobi.Analysis
