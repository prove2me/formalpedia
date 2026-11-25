-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.En.rw_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:51:30.11579+00:00
-- url     : https://prove2.me/submissions/cd4cf74c-2e94-40ae-a5a8-3f7e0893123b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCVLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_rdV_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En
namespace Formalism.FourierDecayAlt.P.CutMP.En
theorem _root_.solution {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (B.Mat k r)}
    (hU : IsOpen U) {f₁ f₂ : B.Mat k r → E} (he : ∀ x ∈ U, x ∈ B.GV k r → f₁ x = f₂ x) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f₁ x = B.Rw w f₂ x
  | [], _, x, hx, hxG => he x hx hxG
  | X :: w, hw, x, hx, hxG => by
    show RdV X (B.Rw w f₁) x = RdV X (B.Rw w f₂) x
    exact Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr hU hx hxG (hw X (by simp))
      (solution hU he w (fun Y hY => hw Y (by simp [hY])))
end Formalism.FourierDecayAlt.P.CutMP.En
