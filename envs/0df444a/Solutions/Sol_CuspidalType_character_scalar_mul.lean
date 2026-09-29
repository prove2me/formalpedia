-- Prove2me | solution 1 for CuspidalType.character_scalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/044e6481-4c30-5bbf-9cde-2bb6013693ec

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_character_scalar_mul

set_option autoImplicit false

open CuspidalType

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (GL2 q) V)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id) (c : (ZMod q)ˣ) (g : GL2 q) :
    ρ.character (scalarElem q c * g) = ρ.character g := by
  simp only [Representation.character, map_mul, hcent c, Module.End.mul_eq_comp, LinearMap.id_comp]

end S_CuspidalType_character_scalar_mul
end P2MW
export P2MW.S_CuspidalType_character_scalar_mul (solution)
