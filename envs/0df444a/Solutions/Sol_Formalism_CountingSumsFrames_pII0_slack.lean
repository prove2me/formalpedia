-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pII0_slack
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:14.140841+00:00
-- url     : https://prove2.me/submissions/d25e4326-8ff7-4112-8c32-5c7d6bfa6663

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
import Theorems.Thm_Formalism_CountingSumsFrames_pII0_basic
import Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_first_term
import Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_second_term
import Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_third_term
import Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_fourth_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real
namespace Formalism.CountingSumsFrames
theorem _root_.solution (r N N₁ k Q c' Y al c₀ : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hrN1 : r ≤ N₁)
    (hN1 : N₁ ^ 2 ≤ r * N) (hk : N₁ + 3 * r ≤ k) (hc : 1 ≤ c') (hY : 0 ≤ Y)
    (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) (hc00 : 0 ≤ c₀) (hc0 : c₀ ≤ c') :
    (100 * r ^ 2 * c' + 24 * (N₁ + r) * c₀ +
        (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1) * (Y * k ^ 2 * Q)
      ≤ 155 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by
  obtain ⟨hrN, hk8, hN1r⟩ := pII0_basic r N N₁ k hr hrN1 hN1 hk
  have hN : 1 ≤ N := by linarith
  have q1 := sizeBound_first_term r N k Q c' Y (by linarith) hN (by linarith) hQ (by linarith) hY
  have q2 := sizeBound_second_term r N N₁ k Q c' Y c₀ (by linarith) hN (by linarith) hQ hY (by linarith) hc00 hc0
  have q3 := sizeBound_third_term r N N₁ k Q c' Y al hQ hr hk8 hc hY hal0 hal (by linarith) (by linarith) hN1r
  have q4 := sizeBound_fourth_term r N k Q c' Y (by linarith) hN (by linarith) hQ hc hY
  have hM : 0 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
    have : 0 ≤ k := by linarith
    have : 0 ≤ N := by linarith
    have : 0 ≤ Q := by linarith
    have : 0 ≤ c' := by linarith
    positivity
  have e : (100 * r ^ 2 * c' + 24 * (N₁ + r) * c₀ +
        (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1) * (Y * k ^ 2 * Q)
      = 100 * (r ^ 2 * c' * (Y * k ^ 2 * Q)) + 24 * ((N₁ + r) * c₀ * (Y * k ^ 2 * Q))
        + (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q)
        + Y * k ^ 2 * Q := by ring
  rw [e]
  linarith
end Formalism.CountingSumsFrames
