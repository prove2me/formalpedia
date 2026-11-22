-- Prove2me | solution 1 for Formalism.Q3.mq_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:29.850852+00:00
-- url     : https://prove2.me/submissions/d8cfe606-6480-40a6-ab9d-a487874ded65

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
variable {k : ℕ} {E : Type} [Field E] [NumberField E] {a : Fin k → ℤ} {α : Fin k → E}
namespace Formalism.Q3
theorem _root_.solution (h : IsMQ a α) (σ : Gal(E/ℚ)) (i : Fin k) :
    σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i := by
  have hsq : (σ (α i)) ^ 2 = (α i) ^ 2 := by
    rw [← map_pow, h.1 i, map_intCast]
  unfold galSign
  split_ifs with hs
  · simp [hs]
  · have : (σ (α i) - α i) * (σ (α i) + α i) = 0 := by ring_nf; rw [hsq]; ring
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hs
    · simp [eq_neg_of_add_eq_zero_left h1]
end Formalism.Q3
