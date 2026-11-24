-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.expFCS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:01:58.192083+00:00
-- url     : https://prove2.me/submissions/83719259-7ced-448a-a42b-c65e0cdebeb2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_comp_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bS_succAbove_last

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
    qminor E (bS f s) (bE c b') u =
      ∑ w : Fin t, ((-1 : ℤ) ^ (w : ℕ)) •
        (Tm E u (f w) c * qminor E (bS f s ∘ w.castSucc.succAbove) b' (u - 1)) +
      ((-1 : ℤ) ^ t) • (Tm E u s c * qminor E f b' (u - 1)) := by
  rw [hFC A n t E (bS f s) (bE c b') u, Fin.sum_univ_castSucc]
  simp only [bE_zero, bE_comp_succ, bS_castSucc, bS_last, bS_succAbove_last, Fin.coe_castSucc, Fin.val_last,
    zsmul_eq_mul]
end Formalism.FourierDecayAlt.P.Qx6
