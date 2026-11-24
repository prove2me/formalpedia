-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVN.span_mul_span1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:17.60438+00:00
-- url     : https://prove2.me/submissions/f046bb6a-ad0e-4a2a-90c7-dc4ef22d87ff

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
theorem _root_.solution (x y : K) :
    Submodule.span (𝓞 K) {x} * Submodule.span (𝓞 K) {y} = Submodule.span (𝓞 K) {x * y} := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]
end Formalism.MainNotions.BridgeLemVN
