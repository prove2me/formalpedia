-- Prove2me | solution 1 for Formalism.Q3.mqFrob_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:48.391149+00:00
-- url     : https://prove2.me/submissions/fd4f37e1-a861-4de9-a7ed-5c4ef47f71e7

import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQFrob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ P.under ℤ) = p := by
  rw [← Ideal.over_def P (span {(p : ℤ)}), Int.card_ideal_quot]
end Formalism.Q3
