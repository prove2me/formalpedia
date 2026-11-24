-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.eichlerMapFixesJointSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:10.021358+00:00
-- url     : https://prove2.me/submissions/038a788b-c53e-4570-9d40-5233ba15272d

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eichlerMapIsometry
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_GoodMap_inN
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eich_good
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eich_perp

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
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.EichlerInR := by
  intro K V _ _ _ _ H r F F' x v c hx hv hc
  have hadm := eich_good eichlerMapIsometry F F' hx hv hc
  obtain ⟨hU, hU'⟩ := Formalism.HermitianLatticeCounting.P.GoodMap.inN F F' hadm
  obtain ⟨-, -, hfix, -⟩ := id hadm
  exact ⟨hfix, hU, hU', fun w hw => eich_perp F F' hx hw⟩
end Formalism.HermitianLatticeCounting.P
