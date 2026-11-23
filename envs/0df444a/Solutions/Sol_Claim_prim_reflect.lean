-- Prove2me | solution 1 for Claim.prim_reflect
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:25.65071+00:00
-- url     : https://prove2.me/submissions/29936825-cd32-4ff0-8dda-569c4ac8fa0c

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_HalfPlane
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ClaimStrip
import Theorems.Thm_Claim_gamma_ne_zero

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
theorem _root_.solution {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction ψ s = 0) :
    DirichletCharacter.LFunction ψ⁻¹ (1 - s) = 0 := by
  have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  have ht0 : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have ht0' : 1 - s ≠ 0 := fun e => by rw [e, Complex.zero_re] at ht0; exact lt_irrefl _ ht0
  have hc : DirichletCharacter.completedLFunction ψ s = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s (Or.inl hs0'),
      div_eq_zero_iff] at h
    exact h.resolve_right (gamma_ne_zero ψ hs0)
  have hψ' : (ψ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hψ
  have fe := hψ'.completedLFunction_one_sub s
  rw [inv_inv, hc, mul_zero] at fe
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s) (Or.inl ht0'), fe,
    zero_div]
end Claim
