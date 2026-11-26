-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r8c_master_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:06.831801+00:00
-- url     : https://prove2.me/submissions/bee35770-fbb6-4d85-9364-c011871b070c

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1Raw_eq_shell
import Theorems.Thm_FourierJacobi_Analysis_i1r10DepthEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r8c_cartan
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10DepthEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10Equiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



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
    (hqt : q*t^2=1) (p : I1R8CRow × ℕ) :
    masterTerm q t d U V T 1 (i1r8cDepthEquiv p).val =
      i1Raw t d U V T p.1.val 1 * collisionProbability q (p.2+1) := by
  rw [i1r8cDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2 + 1) =
      i1Raw t d U V T p.1.val 1 := by
    unfold i1Raw
    rw [i1r8c_cartan, i1r8c_cartan]
    all_goals omega
  rw [he]
  have hc : 2*p.1.val.2.2 = p.1.val.2.1-1 := p.1.property.2.2.2
  simp only [collisionWeight, one_ne_zero, hc, ne_eq, not_true_eq_false, false_or, if_false]
end FourierJacobi.Analysis
