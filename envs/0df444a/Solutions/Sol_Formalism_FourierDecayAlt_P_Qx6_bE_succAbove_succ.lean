-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.bE_succAbove_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:40:56.961802+00:00
-- url     : https://prove2.me/submissions/a1cedb8f-cfdc-4879-805d-c994b354b84b

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
theorem _root_.solution {m : ℕ} (e : Fin n) (v : Fin (m + 1) → Fin n) (w : Fin (m + 1)) :
    bE e v ∘ w.succ.succAbove = bE e (v ∘ w.succAbove) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [bE, Fin.succ_succAbove_zero]
  | succ k => simp [bE, Fin.succ_succAbove_succ]
end Formalism.FourierDecayAlt.P.Qx6
