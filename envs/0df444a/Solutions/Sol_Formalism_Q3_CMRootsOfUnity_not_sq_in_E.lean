-- Prove2me | solution 1 for Formalism.Q3.CMRootsOfUnity.not_sq_in_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:32:36.918101+00:00
-- url     : https://prove2.me/submissions/22cb0287-75e4-4589-92d8-96e69b4e0f8a

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
import Theorems.Thm_Formalism_Q3_CMRootsOfUnity_not_sq_d
import Theorems.Thm_Formalism_Q3_CMRootsOfUnity_not_dvd_one

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
theorem _root_.solution (hK : MQKummer) (hq : Hyp3 q) (hα : IsHost q α) (d : ℤ) (hd : d < 0)
    (hdq : ∀ i, ¬ (q i : ℤ) ∣ d) : ¬ IsSquare (d : E) := by
  intro h
  have hns : ∀ S : Finset (Fin 3), S.Nonempty →
      ¬ IsSquare (∏ i ∈ S, (((-(q i : ℤ)) : ℤ) : ℚ)) := by
    intro S hS
    have := not_sq_d hq 1 S (Or.inl hS) (fun i => by simpa using not_dvd_one hq i)
    simpa using this
  obtain ⟨_, _, hsq⟩ := hK 3 E (fun i => -(q i : ℤ)) α hα hns
  have h' : IsSquare (algebraMap ℚ E (d : ℚ)) := by simpa using h
  obtain ⟨S, hS⟩ := (hsq d).1 h'
  exact not_sq_d hq d S (Or.inr hd) hdq hS
end Formalism.Q3.CMRootsOfUnity
