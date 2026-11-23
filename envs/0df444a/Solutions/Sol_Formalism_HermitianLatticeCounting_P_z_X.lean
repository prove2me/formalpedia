-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.z_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:42.111929+00:00
-- url     : https://prove2.me/submissions/14dbe560-169c-4d6b-aeb3-3203bd5f3e8e

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_isotropicSpan_lastVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (F : FlagD H r) {u : V} (hu : u ∈ F.X) : H.B F.z u = 0 := B_swap0 H ((pairing_isotropicSpan_lastVector F) hu)
end Formalism.HermitianLatticeCounting.P
