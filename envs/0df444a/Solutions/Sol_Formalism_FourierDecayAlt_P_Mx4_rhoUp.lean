-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.rhoUp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:56:40.298467+00:00
-- url     : https://prove2.me/submissions/d5c4f9b3-29b4-4198-968f-fa897fcfdfdf

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_rho_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution : RhoUp := by
  intro P l π π' hU i hi
  have h := Finset.mem_Icc.1 hi
  rw [rho_eq P π i h, rho_eq P π' i h, hU ⟨i - 1, by omega⟩]
  have e : i - 1 + 1 = i := by omega
  simp only [e]
  split_ifs <;> push_cast <;> ring
end Formalism.FourierDecayAlt.P.Mx4
