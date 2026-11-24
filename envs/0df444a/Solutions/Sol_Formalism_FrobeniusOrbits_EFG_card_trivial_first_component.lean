-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.EFG.card_trivial_first_component
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:32:17.154946+00:00
-- url     : https://prove2.me/submissions/566ab3b9-3685-49a0-b92e-16fbfb3ef4d4

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardTrivialFirstComponent
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_card_H


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.EFG
namespace Formalism.FrobeniusOrbits.EFG
theorem _root_.solution (e : ℕ) : Nat.card {g : GG e // g.1 = 1} = 2 ^ e := by
  rw [← Group.card_H e]
  exact Nat.card_congr
    { toFun := fun g => g.1.2
      invFun := fun h => ⟨(1, h), rfl⟩
      left_inv := fun g => by
        obtain ⟨⟨g1, g2⟩, hg⟩ := g
        simp only at hg
        subst hg
        rfl
      right_inv := fun _ => rfl }
end Formalism.FrobeniusOrbits.EFG
