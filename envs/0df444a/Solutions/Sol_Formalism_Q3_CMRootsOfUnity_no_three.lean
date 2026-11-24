-- Prove2me | solution 1 for Formalism.Q3.CMRootsOfUnity.no_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:05.223683+00:00
-- url     : https://prove2.me/submissions/45391a20-93a4-4bba-9758-d1d960ee6791

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
import Theorems.Thm_Formalism_Q3_CMRootsOfUnity_not_sq_in_E

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMRootsOfUnity
variable {q : Fin 3 → ℕ}
variable {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}
namespace Formalism.Q3.CMRootsOfUnity
theorem _root_.solution (hK : MQKummer) (hq : Hyp3 q) (hq3 : ∀ i, q i ≠ 3) (hα : IsHost q α) (ω : E)
    (hω : IsPrimitiveRoot ω 3) : False := by
  have h3 : ω ^ 3 = 1 := hω.pow_eq_one
  have h1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hs : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h1
    · exact h
  refine not_sq_in_E hK hq hα (-3) (by norm_num) (fun i hi => ?_)
    ⟨2 * ω + 1, by push_cast; linear_combination (-4) * hs⟩
  have h3' : q i ∣ 3 := by
    have := dvd_neg.1 hi
    exact_mod_cast this
  exact hq3 i ((Nat.prime_dvd_prime_iff_eq (hq.1 i).1 Nat.prime_three).1 h3')
end Formalism.Q3.CMRootsOfUnity
