-- Prove2me | solution 1 for FourierJacobi.Analysis.i1_basic_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:37.16652+00:00
-- url     : https://prove2.me/submissions/5dd03443-718b-4500-8f8a-b56cb33c3cd0

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
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
theorem _root_.solution (q t : ℂ) (hqt : q*t^2=1) (hz : ‖t^2‖<1) :
    t ≠ 0 ∧ q ≠ 0 ∧ q-1 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    simp [ht] at hqt
  · intro hq
    simp [hq] at hqt
  · intro hq
    have he : q = 1 := sub_eq_zero.mp hq
    have he' : t^2=1 := by simpa only [he,one_mul] using hqt
    rw [he',norm_one] at hz
    exact (lt_irrefl (1 : ℝ)) hz
end FourierJacobi.Analysis
