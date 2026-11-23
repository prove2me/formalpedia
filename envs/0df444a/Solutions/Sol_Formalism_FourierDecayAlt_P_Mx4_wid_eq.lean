-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.wid_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:38.410698+00:00
-- url     : https://prove2.me/submissions/a7161da1-a973-4fe6-b80d-ea4c2b8f9ed8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_lo_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_hi_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_floor_of_int

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
theorem _root_.solution (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : (P.wid i : ℝ) = P.hi i - P.lo i := by
  obtain ⟨a, ha⟩ := lo_int P hP i hi
  obtain ⟨b, hb⟩ := hi_int P hP i hi
  exact floor_of_int _ (by linarith [hP.gap i hi]) (b - a - 1) (by push_cast; linarith)
end Formalism.FourierDecayAlt.P.Mx4
