-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.sign_pair_succAbove_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:54.04196+00:00
-- url     : https://prove2.me/submissions/a59d518d-e314-4630-9cde-b60fc07c73fd

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
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {t : ℕ} (b : Fin (t + 1)) (a : Fin t) :
    sg2 b (b.succAbove a) = (-1) ^ ((b : ℕ) + (a : ℕ)) := by
  unfold sg2
  rcases lt_or_ge (Fin.castSucc a) b with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have h1 : (a : ℕ) < (b : ℕ) := h
    have h' : ((Fin.castSucc a : Fin (t + 1)) : ℕ) < (b : ℕ) := by rw [Fin.coe_castSucc]; exact h1
    rw [if_pos h', Fin.coe_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ h]
    have h1 : (b : ℕ) ≤ (a : ℕ) := h
    have h' : ¬ (((Fin.succ a : Fin (t + 1)) : ℕ) < (b : ℕ)) := by rw [Fin.val_succ]; omega
    rw [if_neg h', Fin.val_succ]
    ring
end Formalism.FourierDecayAlt.P.Qx6
