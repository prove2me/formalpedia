-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1r8c_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:27:32.392972+00:00
-- url     : https://prove2.me/submissions/46b24b48-44c6-4e46-a2ed-a1b56942c606

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1_qinv_eq
import Theorems.Thm_FourierJacobi_Analysis_i1_summable_norm_prob_tail
import Theorems.Thm_FourierJacobi_Analysis_i1_hasSum_product
import Theorems.Thm_FourierJacobi_Analysis_i1r8c_master_reindexed
import Theorems.Thm_FourierJacobi_Analysis_hasSum_collisionProbability_tail
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r8c_raw
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10DepthEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1r8c_raw
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
theorem _root_.solution (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 14 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹)) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r8c_raw t d U V T ht 1 (by omega) h.n h.e
  have hn := summable_norm_i1r8c_raw t d U V T ht 1 (by omega) h.n h.e
  apply i1r8cDepthEquiv.hasSum_iff.mp
  have hg := hasSum_collisionProbability_tail q 0 hq
  simp only [Nat.add_zero, zero_add, pow_one] at hg
  convert i1_hasSum_product (fun p : I1R8CRow => i1Raw t d U V T p.val 1)
    (fun c : ℕ => collisionProbability q (c+1)) _ _ hs hg hn
    (i1_summable_norm_prob_tail q hq) using 1
  exact funext fun p => i1r8c_master_reindexed q t d U V T ht hqt p
end FourierJacobi.Analysis
