-- Prove2me | solution 1 for Claim.strip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:47.364118+00:00
-- url     : https://prove2.me/submissions/52e6e05e-166c-4a9a-a799-02784c0516e8

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_HalfPlane
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ClaimStrip
import Theorems.Thm_Claim_prim_zero
import Theorems.Thm_Claim_prim_reflect

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
theorem _root_.solution (h : HalfPlane) : Strip := by
  unfold HalfPlane at h
  intro N _ χ s hs0 hs1 hz
  have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hp := prim_zero χ hs0 hs1 hz
    have hr := prim_reflect χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hs0 hs1 hp
    have ht : (1 : ℂ) - s ≠ 1 := fun e => hs0' (sub_eq_self.mp e)
    exact h χ.conductor χ.primitiveCharacter⁻¹ (1 - s)
      (by rw [Complex.sub_re, Complex.one_re]; linarith) (Or.inr ht) hr
  · exact heq
  · exact absurd hz (h N χ s hgt (Or.inr hs))
end Claim
