-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ParamsIProof.one_le_log_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:00.501352+00:00
-- url     : https://prove2.me/submissions/b4626f75-9c38-4d3a-9a6e-75c4d1e25ac9

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
theorem _root_.solution (a : ℝ) (ha : 3 ≤ a) : 1 ≤ Real.log a := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]
end Formalism.CountingSumsFrames.ParamsIProof
