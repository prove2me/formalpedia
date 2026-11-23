-- Prove2me | solution 1 for Formalism.CountingSumsFrames.slack_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:11.404438+00:00
-- url     : https://prove2.me/submissions/d711e044-1f63-4d12-90cf-153bfc6cf00e

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSlackBoundsHolds

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
theorem _root_.solution {Y B : ℝ} {k : ℕ} (hM : 0 < Y * (k : ℝ) ^ 2) (hB : 2 * (Y * (k : ℝ) ^ 2) ≤ B) :
    B / (Y * (k : ℝ) ^ 2) / 2 ≤ slII Y k B := by
  unfold slII
  have h1 := Int.sub_one_lt_floor (B / (Y * (k : ℝ) ^ 2))
  have h2 : 2 ≤ B / (Y * (k : ℝ) ^ 2) := by rw [le_div_iff₀ hM]; linarith
  linarith
end Formalism.CountingSumsFrames
