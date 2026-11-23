-- Prove2me | solution 1 for Formalism.Q3.cc_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:23.248964+00:00
-- url     : https://prove2.me/submissions/3641d237-400e-4a68-8cc7-388de55fc250

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.Q3
variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}
namespace Formalism.Q3
theorem _root_.solution (hc : c * c = 1) (g : G) : c * (c * g) = g := by
  rw [← mul_assoc, hc, one_mul]
end Formalism.Q3
