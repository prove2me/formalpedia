-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crv_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:14:39.195854+00:00
-- url     : https://prove2.me/submissions/4e0c72b4-abfc-4610-affb-1f4dc2f07ecf

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
  {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K'] {ι : K →+* K'} {e : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution : Finite (𝓞 K ⧸ la.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
end Formalism.L2.Pj.Crude
