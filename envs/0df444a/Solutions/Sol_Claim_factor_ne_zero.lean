-- Prove2me | solution 1 for Claim.factor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:52.262801+00:00
-- url     : https://prove2.me/submissions/c1ee40eb-1602-44dd-ba83-11bef479e025

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_HalfPlane
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ClaimStrip

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
theorem _root_.solution {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) (p : ℕ)
    (hp : p.Prime) : (1 : ℂ) - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : ψ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hn : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖ψ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by
          gcongr; exact ψ.norm_le_one _
      _ < 1 := by rw [one_mul]; exact hpow
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn
end Claim
