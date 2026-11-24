-- Prove2me | solution 1 for Formalism.Q3.TypesB.mem_image_cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:00.704974+00:00
-- url     : https://prove2.me/submissions/e8ab485e-c034-495f-8053-313a03da3907

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB
import Theorems.Thm_P2M_Formalism_Q3_TypesB_cc_mul__4663f8641e52

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
theorem _root_.solution (hc : c * c = 1) (X : Finset G) (g : G) :
    g ∈ X.image (fun x => c * x) ↔ c * g ∈ X := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
    rwa [cc_mul' hc]
  · intro h
    exact Finset.mem_image.2 ⟨c * g, h, cc_mul' hc g⟩
end Formalism.Q3.TypesB
