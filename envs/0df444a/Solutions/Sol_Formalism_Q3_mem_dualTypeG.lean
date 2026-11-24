-- Prove2me | solution 1 for Formalism.Q3.mem_dualTypeG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:47.405747+00:00
-- url     : https://prove2.me/submissions/82a8b66d-5e6e-4283-b94b-e9ccf7c75a3f

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesA
import Theorems.Thm_Formalism_Q3_cc_mul

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
theorem _root_.solution (hc : c * c = 1) (Φ : Finset G) (g : G) :
    g ∈ dualTypeG c Φ ↔ g = 1 ∨ (c * g ∈ Φ ∧ c * g ≠ 1) := by
  unfold dualTypeG
  rw [Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · rw [Finset.mem_erase] at ha
      rw [cc_mul hc]
      exact Or.inr ⟨ha.2, ha.1⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c * g, Finset.mem_erase.2 ⟨h2, h1⟩, cc_mul hc g⟩
end Formalism.Q3
