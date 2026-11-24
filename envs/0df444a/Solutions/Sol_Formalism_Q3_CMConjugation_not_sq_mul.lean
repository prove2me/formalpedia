-- Prove2me | solution 1 for Formalism.Q3.CMConjugation.not_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:19.342861+00:00
-- url     : https://prove2.me/submissions/9f5fbfa4-e1eb-4c96-8d13-83441c495a9c

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
theorem _root_.solution (p m : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m) : ¬ IsSquare (p * m) := by
  rintro ⟨r, hr⟩
  have h1 : p ∣ r * r := ⟨m, hr.symm⟩
  have h2 : p ∣ r := (hp.dvd_mul.1 h1).elim id id
  obtain ⟨s, rfl⟩ := h2
  apply hm
  have h3 : p * m = p * (s * (p * s)) := by rw [hr]; ring
  rw [Nat.eq_of_mul_eq_mul_left hp.pos h3]
  exact Dvd.intro (s * s) (by ring)
end Formalism.Q3.CMConjugation
