-- Prove2me | solution 1 for CuspidalType.sum_character_mul_character_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0480a8fb-85fc-5b4d-96ed-3a0990dd8d70

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_sum_character_mul_character_inv

set_option autoImplicit false

open CuspidalType

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤) :
    ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q) := by
  classical
  haveI : Representation.IsIrreducible ρ :=
    { exists_pair_ne := ⟨⊥, ⊤, fun h => by
        have h' : (⊥ : Submodule K V) = ⊤ := congrArg Subrepresentation.toSubmodule h
        exact bot_ne_top h'⟩
      eq_bot_or_eq_top := fun W => by
        by_cases h : W.toSubmodule = ⊥
        · exact Or.inl (Subrepresentation.toSubmodule_injective h)
        · exact Or.inr (Subrepresentation.toSubmodule_injective (hirr W h)) }
  have hcard : (Nat.card (GL2 q) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  haveI : Invertible (Nat.card (GL2 q) : K) := invertibleOfNonzero hcard
  have h := Representation.char_orthonormal ρ ρ
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at h
  have h2 := congrArg (fun x => (Nat.card (GL2 q) : K) * x) h
  rwa [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, mul_one] at h2

end S_CuspidalType_sum_character_mul_character_inv
end P2MW
export P2MW.S_CuspidalType_sum_character_mul_character_inv (solution)
