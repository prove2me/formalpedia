-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.weak_to_strong_smoothness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:28.075172+00:00
-- url     : https://prove2.me/submissions/f3a7abc7-de11-4417-b2f1-b309d11e4593

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_weak_to_strong_smoothness_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
namespace Formalism.FourierDecayAlt.P.Ux11
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.WeakToStrong := by
  intro X V E I _ _ _ _ _ _ _ _ lam hN Ω Φ m bd hΩ hbd hcd hb
  exact weak_to_strong_smoothness_real (X := X) (E := E) m V I (fun i => (lam i).restrictScalars ℝ) hN Ω Φ bd hΩ hbd hcd hb
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.Ux11
