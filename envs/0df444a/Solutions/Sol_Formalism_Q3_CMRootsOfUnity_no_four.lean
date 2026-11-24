-- Prove2me | solution 1 for Formalism.Q3.CMRootsOfUnity.no_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:55.401802+00:00
-- url     : https://prove2.me/submissions/b7ebf03b-988a-48cd-bbc8-da1e00d96879

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
import Theorems.Thm_Formalism_Q3_CMRootsOfUnity_not_dvd_one
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
theorem _root_.solution (hK : MQKummer) (hq : Hyp3 q) (hα : IsHost q α) (η : E)
    (hη : IsPrimitiveRoot η 4) : False := by
  have h2 : IsPrimitiveRoot (η ^ 2) 2 := hη.pow (by norm_num) (by norm_num)
  have h := h2.eq_neg_one_of_two_right
  refine not_sq_in_E hK hq hα (-1) (by norm_num) (fun i hi => not_dvd_one hq i ?_)
    ⟨η, by push_cast; linear_combination -h⟩
  exact dvd_neg.1 hi
end Formalism.Q3.CMRootsOfUnity
