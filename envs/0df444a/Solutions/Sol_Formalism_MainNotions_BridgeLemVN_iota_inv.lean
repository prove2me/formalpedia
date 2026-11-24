-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVN.iota_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:39:03.21582+00:00
-- url     : https://prove2.me/submissions/497bb988-7120-4db3-8b0d-b6739cd31137

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVN
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVN
theorem _root_.solution (x : (𝓞 (cmF K))ˣ) : iota K x⁻¹ = (iota K x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
end Formalism.MainNotions.BridgeLemVN
