-- Prove2me | solution 1 for Formalism.Q3.CMRootsOfUnity.gal_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:25.660813+00:00
-- url     : https://prove2.me/submissions/341e6073-ed0f-4392-a1c0-f1af2cf0477f

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu

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
theorem _root_.solution (hH : HostGalois) (hq : Hyp3 q) (hα : IsHost q α) (σ : Gal(E/ℚ)) :
    σ * σ = 1 := by
  obtain ⟨_, _, hbij, hmul⟩ := hH q hq E α hα
  apply hbij.1
  rw [hmul]
  funext i
  have h1 : galSign α (1 : Gal(E/ℚ)) i = 1 := by simp [galSign]
  rw [Pi.mul_apply, h1, Int.units_mul_self]
end Formalism.Q3.CMRootsOfUnity
