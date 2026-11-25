-- Prove2me | solution 1 for Formalism.Q3.key_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:25.73805+00:00
-- url     : https://prove2.me/submissions/e27a53d8-7de6-4b98-a7b5-e5736852fb62

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesA
import Theorems.Thm_Formalism_Q3_mem_dualTypeG
import Theorems.Thm_P2M_Formalism_Q3_mul_ne_one_iff__67a0a7119a81

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
theorem _root_.solution (hc : c * c = 1) {Φ : Finset G} (hΦ : IsCMTypeG c Φ) (σ : G) (h1 : σ ≠ 1)
    (h2 : σ ≠ c) : σ ∈ dualTypeG c Φ ↔ σ ∉ Φ := by
  rw [mem_dualTypeG hc, hΦ σ, not_not]
  have := (mul_ne_one_iff' hc σ).2 h2
  tauto
end Formalism.Q3
