-- Prove2me | solution 1 for ExtCitation.map_primitiveRoot_eq_pow_cycloExp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1c06d37f-be0b-5ea2-ae59-e10c65728f3d

import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_map_primitiveRoot_eq_pow_cycloExp

open ExtCitation
open ValuationSubring
variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]

theorem solution (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {ξ : AlgebraicClosure ℚ} (hξ : IsPrimitiveRoot ξ p) : σ ξ = ξ ^ cycloExp p σ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hspec := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
    (card_rootsOfUnity_eq_self p) (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)
    (SetLike.coe_mem hξ.toRootsOfUnity)
  rw [cycloExp]
  simpa [hξ.val_toRootsOfUnity_coe, Units.val_pow_eq_pow_val] using hspec

end S_ExtCitation_map_primitiveRoot_eq_pow_cycloExp
end P2MW
export P2MW.S_ExtCitation_map_primitiveRoot_eq_pow_cycloExp (solution)
