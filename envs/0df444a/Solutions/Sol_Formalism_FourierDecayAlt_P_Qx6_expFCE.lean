-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.expFCE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:04:36.3369+00:00
-- url     : https://prove2.me/submissions/dc3cdcd1-9d20-4e7d-8866-0b9129e90321

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_comp_succ
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
theorem _root_.solution (hFC : ExpFirstCol) {t : ℕ} (f b' : Fin t → Fin n) (s c : Fin n) (u : ℂ) :
    qminor E (bE s f) (bE c b') u = Tm E u s c * qminor E f b' (u - 1) +
      ∑ w : Fin t, ((-1 : ℤ) ^ ((w : ℕ) + 1)) •
        (Tm E u (f w) c * qminor E (bE s f ∘ w.succ.succAbove) b' (u - 1)) := by
  rw [hFC A n t E (bE s f) (bE c b') u, Fin.sum_univ_succ]
  simp only [bE_zero, bE_succ, bE_comp_succ, bE_succAbove_zero, Fin.val_zero, Fin.val_succ, pow_zero,
    Int.cast_one, one_mul, zsmul_eq_mul]
end Formalism.FourierDecayAlt.P.Qx6
