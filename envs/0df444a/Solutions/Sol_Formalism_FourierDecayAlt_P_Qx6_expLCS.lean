-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.expLCS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:06.23399+00:00
-- url     : https://prove2.me/submissions/dff791a1-d0c6-48d4-8919-b69ab16bd77a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bS_comp_castSucc
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
theorem _root_.solution (hLC : ExpLastCol) {t : ℕ} (f b' : Fin t → Fin n) (s c : Fin n) (u : ℂ) :
    qminor E (bS f s) (bS b' c) u =
      ∑ w : Fin t, ((-1 : ℤ) ^ (t + (w : ℕ))) •
        (qminor E (bS f s ∘ w.castSucc.succAbove) b' u * Tm E (u - (t : ℂ)) (f w) c) +
      qminor E f b' u * Tm E (u - (t : ℂ)) s c := by
  have h2 : ((-1 : ℤ) ^ (t + t)) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  rw [hLC A n t E (bS f s) (bS b' c) u, Fin.sum_univ_castSucc]
  simp only [bS_comp_castSucc, bS_last, bS_castSucc, bS_succAbove_last, Fin.coe_castSucc, Fin.val_last, h2,
    Int.cast_one, one_mul, zsmul_eq_mul]
end Formalism.FourierDecayAlt.P.Qx6
