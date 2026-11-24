-- Prove2me | solution 1 for Formalism.ResultantValuation.ParabolicCounting.lequiv_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:47.080135+00:00
-- url     : https://prove2.me/submissions/1bcd6175-edc7-4539-9746-bf9c799baf20

import Definitions.Def_Formalism_ResultantValuation_SubspaceCount
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ResultantValuation
open Module
open Formalism.ResultantValuation.ParabolicCounting
variable (F : Type) [Field F] (r t : ℕ)
attribute [local instance] act
namespace Formalism.ResultantValuation.ParabolicCounting
theorem _root_.solution (g : GL (Fin (r + t)) F) :
    ((lequiv F r t g : (Fin (r + t) → F) ≃ₗ[F] (Fin (r + t) → F)) :
        (Fin (r + t) → F) →ₗ[F] (Fin (r + t) → F)) =
      Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F) := by
  rw [lequiv, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
    Matrix.GeneralLinearGroup.coe_toLin]
end Formalism.ResultantValuation.ParabolicCounting
