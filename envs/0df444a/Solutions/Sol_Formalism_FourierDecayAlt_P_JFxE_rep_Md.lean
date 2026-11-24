-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.rep_Md
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:44.019795+00:00
-- url     : https://prove2.me/submissions/b533b0fa-4941-47cd-9043-ea0a07f01e13

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rep_rel
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rep_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {m : ℕ} (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m) :
    Rep 2 (Md (Lf k r E) a b σ i) := by
  unfold Md
  exact rep_add (rep_rel _ _ _ _) (rep_rel _ _ _ _)
end Formalism.FourierDecayAlt.P.JFxE
