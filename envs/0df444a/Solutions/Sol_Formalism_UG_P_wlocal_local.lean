-- Prove2me | solution 1 for Formalism.UG.P.wlocal_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:22.359836+00:00
-- url     : https://prove2.me/submissions/03be4266-2046-464b-82a6-66f4bb3c0475

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.WeylGLStableLocal := by
  intro R _ _ r n hn ν g f hf
  exact wlocal_main hn ν r 0 (by omega) _ _ (Units.mul_inv g) (fun i j hj => absurd hj (Nat.not_lt_zero _)) f hf
end Formalism.UG.P
