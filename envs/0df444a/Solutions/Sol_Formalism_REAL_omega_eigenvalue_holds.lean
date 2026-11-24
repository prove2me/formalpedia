-- Prove2me | solution 1 for Formalism.REAL.omega_eigenvalue_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:45:10.392511+00:00
-- url     : https://prove2.me/submissions/1733d912-5be8-46e8-98c3-c130ec41b985

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Theorems.Thm_Formalism_REAL_rho_nsq_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : OmEigen := by
  intro n ε lam a b hab
  have e : lam + rhoN ε - rhoC ε + root a b + rhoC ε = (lam + rhoN ε - rhoC ε + rhoC ε) + root a b := by
    abel
  rw [e, rho_nsq_root _ a b hab]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring
end Formalism.REAL
