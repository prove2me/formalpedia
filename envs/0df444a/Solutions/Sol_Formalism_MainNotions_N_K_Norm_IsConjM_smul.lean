-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.IsConjM.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:58.020625+00:00
-- url     : https://prove2.me/submissions/c14bc80e-b412-4f37-ab09-786f1f1bc6b7

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {Γ : Type} {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.MainNotions.N.K.Norm
namespace IsConjM
theorem _root_.solution {M M' : Γ → Matrix n n K} (h : IsConjM M M') (c : Γ → K) :
    IsConjM (fun g => c g • M g) (fun g => c g • M' g) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, fun g => by rw [Matrix.mul_smul, Matrix.smul_mul, h3]⟩
end IsConjM
end Formalism.MainNotions.N.K.Norm
