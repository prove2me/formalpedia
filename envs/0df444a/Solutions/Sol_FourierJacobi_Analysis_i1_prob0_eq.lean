-- Prove2me | solution 1 for FourierJacobi.Analysis.i1_prob0_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:57.45615+00:00
-- url     : https://prove2.me/submissions/86a487a6-2b08-48fd-aa20-b46b1a658e8c

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1_qinv_eq
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10DepthEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10Equiv_val
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
theorem _root_.solution (q t : ℂ) (ht : t ≠ 0) (hqt : q*t^2=1)
    (hz : 1-t^2 ≠ 0) : collisionProbability q 0 = (1-2*t^2)/(1-t^2) := by
  have he : q = (t^2)⁻¹ := by
    rw [← i1_qinv_eq q t ht hqt, inv_inv]
  simp only [collisionProbability, if_true]
  rw [he]
  field_simp [ht,hz]
  <;> ring
end FourierJacobi.Analysis
