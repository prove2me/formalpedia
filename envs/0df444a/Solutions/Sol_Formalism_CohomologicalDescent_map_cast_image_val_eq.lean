-- Prove2me | solution 1 for Formalism.CohomologicalDescent.map_cast_image_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:15.029225+00:00
-- url     : https://prove2.me/submissions/f3932a79-81d0-4dbf-96d0-13d72b64750c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_WEChain
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ContentLinkageHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution (l N : ℕ) (W : Fin N → ℤ) (hW : StrictAnti W) :
    Multiset.map (fun u : ℤ => (u : ZMod l)) (Finset.univ.image W).val =
      Multiset.map (fun a => ((W a : ℤ) : ZMod l)) Finset.univ.val := by
  rw [Finset.image_val_of_injOn hW.injective.injOn, Multiset.map_map]
  rfl
end Formalism.CohomologicalDescent
