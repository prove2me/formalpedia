-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.preserves_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:59:19.781149+00:00
-- url     : https://prove2.me/submissions/0c1d2eb8-f1df-4ee3-914f-8d743222c959

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_preserves_transfer_letter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_preserves_transfer_letter_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_preserves_operator_mul

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
theorem _root_.solution {R : Fn k r E → Fn k r E → Prop} (hR : LinRel R) (Y : ℂ) : ∀ (j : ℕ)
    (_ : ∀ l : Fin r, l.val < j → ∀ q, Pres2 R (crd (opL l q)) (crd (opL l q))) {M M' : OM (Fn k r E)}
    (_ : ∀ a b, Pres2 R (M a b) (M' a b)) (a b : Fin 2), Pres2 R (sandw k r Y j M a b) (sandw k r Y j M' a b)
  | 0, _, _, _, hM, a, b => hM a b
  | j + 1, h, M, M', hM, a, b => by
    show Pres2 R (sandw k r Y j _ a b) (sandw k r Y j _ a b)
    refine solution hR Y j (fun l hl => h l (Nat.lt_succ_of_lt hl)) ?_ a b
    intro a b
    by_cases hj : j < r
    · simp only [dif_pos hj]
      exact preserves_operator_mul hR (preserves_transfer_letter_star hR _ (h ⟨j, hj⟩ (Nat.lt_succ_self j)) Y)
        (preserves_operator_mul hR hM (preserves_transfer_letter hR _ (h ⟨j, hj⟩ (Nat.lt_succ_self j)) Y)) a b
    · simp only [dif_neg hj]
      exact hM a b
end Formalism.FourierDecayAlt.P.Qx6
