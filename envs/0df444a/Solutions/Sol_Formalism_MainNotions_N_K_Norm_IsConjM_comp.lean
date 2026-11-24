-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.IsConjM.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:11.097939+00:00
-- url     : https://prove2.me/submissions/68053e39-578a-486d-9bf1-ca5f2f81b192

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
theorem _root_.solution {M M' : Γ → Matrix n n K} (h : IsConjM M M') {Γ' : Type} (f : Γ' → Γ) :
    IsConjM (fun g => M (f g)) (fun g => M' (f g)) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, fun g => h3 (f g)⟩
end IsConjM
end Formalism.MainNotions.N.K.Norm
