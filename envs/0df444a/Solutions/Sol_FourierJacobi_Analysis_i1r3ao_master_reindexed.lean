-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r3ao_master_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:59.327895+00:00
-- url     : https://prove2.me/submissions/a8b80f63-307c-4e36-84f0-f4970e3b0746

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1Raw_eq_shell
import Theorems.Thm_FourierJacobi_Analysis_i1r3ao_cartan


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
    (hqt : q*t^2=1) (p : I1R3AORow × ℕ) :
    masterTerm q t d U V T 1 (i1r3aoDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r3aoDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r3ao_cartan, i1r3ao_cartan]
    
  rw [he]
end FourierJacobi.Analysis
