-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.wachLatticeUnramified_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:18:16.501853+00:00
-- url     : https://prove2.me/submissions/bdad8152-8ec4-48ff-88de-f1333e04db78

import Definitions.Def_Formalism_LagrangeIdealLifts_LiftLagrangeIdealInt
import Definitions.Def_Formalism_CoboundaryTransfers_StatementBridge
import Definitions.Def_Formalism_CoboundaryTransfers_StatementTransfer
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_Transfer
import Theorems.Thm_Formalism_LIFT_lift_LemmaU


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
open Formalism
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : LemmaUU := by
  intro ℓ _ A _ _ B M u hp hφ hγX hγQ D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e s J hs h2 hv
    hJ h1 h2' h3 h4 hCK hRS
  have hCK' : LIFT.CokerKilled (sesToLIFT S u hφ hγX hγQ) e := by
    intro n hn
    have := hCK n hn
    rw [hp] at this
    exact this
  have hRS' : LIFT.RatSurj (sesToLIFT S u hφ hγX hγQ) := by
    intro y z hyz
    have := hRS y z hyz
    rw [hp] at this
    exact this
  exact LIFT.lift_LemmaU ℓ A (toLIFT B u hφ hγX hγQ) M D₀ D₁ D₂ (W₀.toLIFT u hφ hγX hγQ)
    (W₁.toLIFT u hφ hγX hγQ) (W₂.toLIFT u hφ hγX hγQ) (sesToLIFT S u hφ hγX hγQ) e s J hs h2 hv
    hJ h1 h2' h3 h4 hCK' hRS'
end Formalism.CoboundaryTransfers
