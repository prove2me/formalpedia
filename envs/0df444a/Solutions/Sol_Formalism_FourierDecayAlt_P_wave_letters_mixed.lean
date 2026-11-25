-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.wave_letters_mixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:54:02.66783+00:00
-- url     : https://prove2.me/submissions/17bcaa20-bd9c-4b51-8121-e384697d7263

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdBelowOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx11_chebToThreshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx11_mix

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
theorem _root_.solution : WaveLettersMix := by
  intro hPW hCS R M _ _ _ _ _ _ Ξ n L f pl dat α β X X' κ len Mj lv be hn hκ hlen hbt hsh hs hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have hd : 1 ≤ 2 * n := by omega
  have hid := hPW R M Ξ n L dat (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n)) X X' hsh
    (fun a => (hCS (α a) (β a) (2 * n) (hlt a) hd).1)
  obtain ⟨m1, m2, m3⟩ := mix (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n))
    (fun a => (1 / 2) * (4 / (β a - α a)) ^ (2 * n))
    (fun a => (hCS (α a) (β a) (2 * n) (hlt a) hd).2)
    (fun a => by have := hlt a; have h : 0 < β a - α a := by linarith
                 positivity)
    _ _ hid _ Mj hF
  refine ⟨m1, m2, ?_⟩
  rw [norm_mul, norm_prod] at m3
  exact chebToThreshold L f (2 * n) pl (fun a => ‖(dat a).s‖) α β κ len lv be _ _ _ hκ hlen hbt hs
    m3 le_rfl
end Formalism.FourierDecayAlt.P
