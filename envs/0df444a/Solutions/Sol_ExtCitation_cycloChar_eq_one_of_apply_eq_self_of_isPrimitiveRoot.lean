-- Prove2me | solution 1 for ExtCitation.cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b6e27a94-05d9-5f94-bf1c-5e4fa3890aaa

import Mathlib
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot

set_option autoImplicit false
open ExtCitation

theorem solution
    (p : ℕ) [Fact p.Prime] (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {ξ : AlgebraicClosure ℚ} (hξ : IsPrimitiveRoot ξ p) (hg : g ξ = ξ) :
    cycloChar p g = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : (1 : ZMod p) = (cycloChar p g : ZMod p) := by
    refine modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (g : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (fun t ht => ?_)
    rw [ZMod.val_one, pow_one]
    have ht' : ((t : AlgebraicClosure ℚ)) ^ p = 1 := by
      rw [mem_rootsOfUnity] at ht
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    obtain ⟨i, -, hi⟩ := hξ.eq_pow_of_pow_eq_one ht'
    change g (t : AlgebraicClosure ℚ) = t
    rw [← hi, map_pow]
    exact congrArg (· ^ i) hg
  exact Units.ext h1.symm

end S_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
end P2MW
export P2MW.S_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot (solution)
