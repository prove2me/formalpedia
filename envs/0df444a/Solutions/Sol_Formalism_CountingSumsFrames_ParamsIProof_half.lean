-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ParamsIProof.half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:29:52.994513+00:00
-- url     : https://prove2.me/submissions/a2f95667-34d9-40ac-90d1-c8b5cbbc48ed

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ParamsI

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
open Formalism.CountingSumsFrames.ParamsIProof
namespace Formalism.CountingSumsFrames.ParamsIProof
theorem _root_.solution (Yb : ℝ) (N : ℕ) (hYb : 4 ≤ Yb) (hN : 1 ≤ N) :
    1 / 2 ≤ (1 - 2 / (Yb * N)) ^ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hYb0 : 0 < Yb := by linarith
  have h2 : 2 / (Yb * N) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have key := one_add_mul_le_pow (a := -(2 / (Yb * N))) (by linarith) N
  have e1 : (N : ℝ) * (-(2 / (Yb * N))) = -(2 / Yb) := by field_simp
  have e2 : 2 / Yb ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hYb0 (by norm_num)]
    linarith
  rw [show (1 : ℝ) - 2 / (Yb * N) = 1 + -(2 / (Yb * N)) by ring]
  linarith
end Formalism.CountingSumsFrames.ParamsIProof
