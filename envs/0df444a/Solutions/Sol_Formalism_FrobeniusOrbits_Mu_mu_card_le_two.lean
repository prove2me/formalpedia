-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Mu.mu_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:15:46.399622+00:00
-- url     : https://prove2.me/submissions/75c8dde0-6c6f-44c7-9b89-cfb6df45e6f7

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_MuCardLeTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Mu
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.FrobeniusOrbits.Mu
theorem _root_.solution {G : Type*} [One G] (f : Gal(L/ℚ) → G) (hinj : Function.Injective f)
    (t : G) (H : Subgroup Gal(L/ℚ)) (hH : ∀ ρ ∈ H, f ρ = 1 ∨ f ρ = t) : Nat.card H ≤ 2 := by
  classical
  let g : H → ({1, t} : Set G) := fun ρ => ⟨f ρ, by rcases hH ρ ρ.2 with h | h <;> simp [h]⟩
  have hg : Function.Injective g := fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy))
  calc Nat.card H ≤ Nat.card ({1, t} : Set G) := Nat.card_le_card_of_injective g hg
    _ = ({1, t} : Set G).ncard := by first | exact Nat.card_coe_set_eq _ | exact Set.Nat.card_coe_set_eq _
    _ ≤ 2 := (Set.ncard_insert_le 1 {t}).trans (by simp)
end Formalism.FrobeniusOrbits.Mu
