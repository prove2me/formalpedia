-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sizeBound_third_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:57.104362+00:00
-- url     : https://prove2.me/submissions/f5bc8f32-5c94-4d26-a3d4-fc90bcbfe452

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
import Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_multiplicity_le

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
theorem _root_.solution (r N N₁ k Q c' Y al : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hk8 : 8 ≤ k) (hc : 1 ≤ c')
    (hY : 0 ≤ Y) (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) (hN0 : 0 ≤ N) (hN10 : 0 ≤ N₁)
    (hN1r : N₁ + 1 ≤ 2 * r * N) :
    (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q)
      ≤ 6 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by
  have hS3 := sizeBound_multiplicity_le r k Q c' al hQ hr hk8 hc hal
  have hS0 : 0 ≤ (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' := by
    have : 0 ≤ c' * al := by nlinarith
    nlinarith
  have hW : 0 ≤ Y * k ^ 2 * Q := by positivity
  have e1 : (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') ≤ (2 * r * N) * (3 * r * k * c' * Q) :=
    mul_le_mul hN1r hS3 hS0 (by positivity)
  have h1 : Q ^ 2 ≤ Q ^ 5 := pow_le_pow_right₀ hQ (by norm_num)
  have h0 : 0 ≤ 6 * r ^ 2 * N * k ^ 3 * c' * Y := by positivity
  calc (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q)
      ≤ (2 * r * N) * (3 * r * k * c' * Q) * (Y * k ^ 2 * Q) := mul_le_mul_of_nonneg_right e1 hW
    _ = (6 * r ^ 2 * N * k ^ 3 * c' * Y) * Q ^ 2 := by ring
    _ ≤ (6 * r ^ 2 * N * k ^ 3 * c' * Y) * Q ^ 5 := mul_le_mul_of_nonneg_left h1 h0
    _ = 6 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by ring
end Formalism.CountingSumsFrames
