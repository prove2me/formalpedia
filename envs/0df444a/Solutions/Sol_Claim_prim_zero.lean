-- Prove2me | solution 1 for Claim.prim_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:26.174826+00:00
-- url     : https://prove2.me/submissions/60e3b674-f7b2-4dc9-9922-ce356b159e0c

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_HalfPlane
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ClaimStrip
import Theorems.Thm_Claim_factor_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open Claim
namespace Claim
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
  have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  have key := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter (Or.inr hs)
  rw [χ.changeLevel_primitiveCharacter, h] at key
  rcases mul_eq_zero.mp key.symm with h' | h'
  · exact h'
  · obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.mp h'
    exact absurd hp0 (factor_ne_zero _ hs0 p (Nat.prime_of_mem_primeFactors hp))
end Claim
