-- Prove2me | solution 1 for Formalism.CountingSumsFrames.cloud_share_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:19.121994+00:00
-- url     : https://prove2.me/submissions/2e41253c-27d8-46f3-96f5-90b7100145bf

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : CloudShare := by
  intro ρ dcl dH dHp dlam κH κHp x hdlam hdH hdHp hdcl hκH0 hκH1 hκHp hx0 hx1 hρ h1 h2 h3
  have hQ : dcl * dHp ≤ (1 + x) * (dcl * dH) := by
    have := mul_le_mul_of_nonneg_left h2 hdcl; nlinarith
  have hP1 : (1 - κH) * ((1 - x) * dlam) ≤ (1 - κH) * (dcl * dH) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have hQ2 : κHp * (dcl * dHp) ≤ κHp * (2 * dlam) := by
    apply mul_le_mul_of_nonneg_left _ hκHp; nlinarith
  have hkx : 0 ≤ κH * x * dlam := by positivity
  have key : (1 - κH - 2 * κHp - x) * dlam ≤ ρ := by nlinarith
  have : 1 - κH - 2 * κHp - x ≤ ρ / dlam := by rw [le_div_iff₀ hdlam]; linarith
  linarith
end Formalism.CountingSumsFrames
