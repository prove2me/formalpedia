-- Prove2me | solution 1 for Formalism.Q3.CMConjugation.sigma_alpha
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:24.233772+00:00
-- url     : https://prove2.me/submissions/3d898dca-46d8-4b27-a8bb-0773b35975da

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMConjugation
variable {q : Fin 3 → ℕ} {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}
namespace Formalism.Q3.CMConjugation
theorem _root_.solution (hα : IsHost q α) (σ : Gal(E/ℚ)) (i : Fin 3) :
    σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i := by
  have hsq : σ (α i) ^ 2 = α i ^ 2 := by
    rw [← map_pow, hα.1 i, map_intCast]
  unfold galSign
  split_ifs with hc
  · simp [hc]
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
    · exact absurd h1 hc
    · simp [h1]
end Formalism.Q3.CMConjugation
