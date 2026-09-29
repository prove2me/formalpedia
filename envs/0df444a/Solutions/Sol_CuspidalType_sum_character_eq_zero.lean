-- Prove2me | solution 1 for CuspidalType.sum_character_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/51eaff43-3cde-527b-b633-536e606eae23

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_sum_character_eq_zero

set_option autoImplicit false

open CuspidalType

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) :
    ∑ g : GL2 q, ρ.character g = 0 := by
  classical
  have he : ∑ g : GL2 q, ρ g = 0 := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.coe_sum, Finset.sum_apply, LinearMap.zero_apply]
    apply hcusp
    intro t
    rw [map_sum]
    calc ∑ g : GL2 q, ρ (unipotent q t) (ρ g v) = ∑ g : GL2 q, ρ (unipotent q t * g) v := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ∑ g : GL2 q, ρ g v :=
          Fintype.sum_equiv (Equiv.mulLeft (unipotent q t)) _ _ (fun g => rfl)
  have h : ∑ g : GL2 q, ρ.character g = LinearMap.trace K V (∑ g : GL2 q, ρ g) := by
    rw [map_sum]; rfl
  rw [h, he, map_zero]

end S_CuspidalType_sum_character_eq_zero
end P2MW
export P2MW.S_CuspidalType_sum_character_eq_zero (solution)
