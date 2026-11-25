-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lift_letters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:32.89513+00:00
-- url     : https://prove2.me/submissions/557269ee-ec22-4333-9adb-768645948a8d

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdBelowOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx11
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : LiftLetters := by
  intro hLW hC R M _ _ _ _ _ _ Ξ n s L f pl dat A₀ A₀v e t t' α β X X' κ len Mx ov be hs hκ hlen hbt
    h0 he ht hA hA0 hB hBv ho hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have h1 := hLW R M Ξ n s L dat A₀ A₀v e t t' α β X X' _ hs h0 he ht hA hA0 hB hBv hlt hF
  exact hC L f (2 * n + s) pl (fun a => ‖1 / t a - 1 / t' a‖) α β κ len ov be _ _ Mx hκ hlen hbt ho h1 le_rfl
end Formalism.FourierDecayAlt.P
