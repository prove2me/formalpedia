-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.expLCE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:00:40.271359+00:00
-- url     : https://prove2.me/submissions/e24a5405-4007-4029-8b86-cdacbc5aa7c8

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bS_comp_castSucc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_succAbove_zero
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
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hLC : ExpLastCol) {t : ℕ} (f b' : Fin t → Fin n) (s c : Fin n) (u : ℂ) :
    qminor E (bE s f) (bS b' c) u =
      ((-1 : ℤ) ^ t) • (qminor E f b' u * Tm E (u - (t : ℂ)) s c) +
      ∑ w : Fin t, ((-1 : ℤ) ^ (t + ((w : ℕ) + 1))) •
        (qminor E (bE s f ∘ w.succ.succAbove) b' u * Tm E (u - (t : ℂ)) (f w) c) := by
  rw [hLC A n t E (bE s f) (bS b' c) u, Fin.sum_univ_succ]
  simp only [bS_comp_castSucc, bS_last, bE_zero, bE_succ, bE_succAbove_zero, Fin.val_zero, Fin.val_succ, add_zero,
    zsmul_eq_mul]
end Formalism.FourierDecayAlt.P.Qx6
