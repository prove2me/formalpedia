-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.bE_cyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:41:04.182534+00:00
-- url     : https://prove2.me/submissions/fe6d9341-ae60-4602-9e0a-9e3488fcdf1b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {n : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bE e v ∘ cycleToLast m 0 = bS v e := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    have h : cycleToLast m 0 (Fin.last m) = 0 := by
      simp only [cycleToLast, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_last, Fin.rev_zero, Fin.cycleRange_symm_zero]
    rw [Function.comp_apply, h, bS_last, bE_zero]
  | cast k =>
    have h : cycleToLast m 0 (Fin.castSucc k) = k.succ := by
      simp only [cycleToLast, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_zero, Fin.cycleRange_symm_succ,
        Fin.succAbove_last, Fin.rev_rev]
    rw [Function.comp_apply, h, bS_castSucc, bE_succ]
end Formalism.FourierDecayAlt.P.Qx6
