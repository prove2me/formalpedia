-- Prove2me | solution 1 for Formalism.SLP.P.CountO.nsmul_mem_mulSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:30.175225+00:00
-- url     : https://prove2.me/submissions/40725953-1c28-4597-992b-b23ce389e9b4

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
namespace Formalism.SLP.P.CountO
theorem _root_.solution (c : ℕ) (x : X) : c • x ∈ mulSub R X c := ⟨x, by simp⟩
end Formalism.SLP.P.CountO
