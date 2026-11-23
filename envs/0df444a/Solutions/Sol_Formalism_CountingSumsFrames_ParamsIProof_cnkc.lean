-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ParamsIProof.cnkc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:27.568732+00:00
-- url     : https://prove2.me/submissions/8236a823-8019-45c3-af96-4e87b0674100

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
theorem _root_.solution (C Ck k Y Nr cl b' : ℝ) (hCk : 1 ≤ Ck) (hC : 1000 * Ck ≤ C) (hk : 1 ≤ k) (hY : 1 ≤ Y)
    (hN : 0 ≤ Nr) (hcl : 0 ≤ cl) (hb : 0 < b') (hM : C * k ^ 3 * Y * (Nr * cl) ≤ b') :
    Ck * Nr * k * (2 * cl) / b' ≤ 1 / Y := by
  rw [div_le_div_iff₀ hb (by linarith)]
  have hk3 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have h1 : 2 * Ck * k ≤ C * k ^ 3 := by nlinarith
  have h2 : 2 * Ck * k * (Y * (Nr * cl)) ≤ C * k ^ 3 * (Y * (Nr * cl)) :=
    mul_le_mul_of_nonneg_right h1 (mul_nonneg (by linarith) (mul_nonneg hN hcl))
  linarith
end Formalism.CountingSumsFrames.ParamsIProof
