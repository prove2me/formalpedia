-- Prove2me | solution 1 for Formalism.Q3.TypesB.mem_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:28:17.968969+00:00
-- url     : https://prove2.me/submissions/b2266445-62c5-411d-92f0-a45e413ec181

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB
import Theorems.Thm_Formalism_Q3_TypesB_mem_image_cmul

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
open Formalism.Q3.TypesB
variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}
namespace Formalism.Q3.TypesB
theorem _root_.solution (hc : c * c = 1) (H S : Finset G) (x : G) :
    x ∈ ext c H S ↔ x ∈ S ∨ (c * x ∈ H ∧ c * x ∉ S) := by
  unfold ext
  rw [mem_union, mem_image_cmul hc, mem_sdiff]
end Formalism.Q3.TypesB
