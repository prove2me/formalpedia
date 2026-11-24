-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.preserves_transfer_letter_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:37:58.608794+00:00
-- url     : https://prove2.me/submissions/548b8b91-3db4-4448-9144-45745c31dcac

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul


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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {R : Fn k r E → Fn k r E → Prop} (hR : LinRel R) (l : Fin r)
    (h : ∀ q, Pres2 R (crd (opL l q)) (crd (opL l q))) (Y : ℂ) (a b : Fin 2) :
    Pres2 R (TLs k l Y a b) (TLs k l Y a b) := by
  intro Φ Ψ hΦ
  fin_cases a <;> fin_cases b
  · exact hR.sub (hR.smul Y hΦ) (h 3 _ _ hΦ)
  · exact h 5 _ _ hΦ
  · exact hR.neg (h 4 _ _ hΦ)
  · exact hR.zero
end Formalism.FourierDecayAlt.P.Qx6
