-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.EFG.card_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:57:07.192902+00:00
-- url     : https://prove2.me/submissions/d5030937-0ed4-4222-a6ba-8653cefdd132

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardTrivialFirstComponent
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_card_H
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_card_units_int


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
theorem _root_.solution (e : ℕ) : Nat.card (Psi e) = 2 ^ (e + 1) := by
  have hmem : ∀ g : GG e, g ∈ Psi e ↔ g.1.2 = 1 := fun g => by
    simp [Psi, chD, MonoidHom.mem_ker]
  have : Nat.card (Psi e) = Nat.card (ℤˣ × HGrp e) :=
    Nat.card_congr
      { toFun := fun g => (g.1.1.1, g.1.2)
        invFun := fun x => ⟨((x.1, 1), x.2), (hmem _).2 rfl⟩
        left_inv := fun g => by
          obtain ⟨⟨⟨g1, g2⟩, g3⟩, hg⟩ := g
          have h2 : g2 = 1 := (hmem _).1 hg
          subst h2
          rfl
        right_inv := fun _ => rfl }
  rw [this, Nat.card_prod, Group.card_H, Nat.card_eq_fintype_card, Fintype.card_units_int]
  ring
end Formalism.FrobeniusOrbits.EFG
