-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.landau_local3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:17.281786+00:00
-- url     : https://prove2.me/submissions/c2f570c4-2094-49d0-8b3f-92497bc2e617

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExistsLocalZeroExpansionOfBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
import Theorems.Thm_Formalism_ZeroFreeDirichlet_exists_localZeroExpansion_of_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : LandauLocal3 :=
  fun f z₀ r M hr hM hf hfz₀ hbound => exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound
end Formalism.ZeroFreeDirichlet
