-- Prove2me | solution 1 for Formalism.CountingSumsFrames.slackBound_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:57.502781+00:00
-- url     : https://prove2.me/submissions/281d53d7-51bd-48db-b147-d46644b43bdb

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
theorem _root_.solution {M P B c : ℝ} (hM : 0 < M) (hc : 0 < c) (hB : 0 ≤ B) (hP : 16 * c * M ≤ P) :
    c * P⁻¹ * B ≤ B / M / 2 / 8 := by
  have hP0 : 0 < 16 * c * M := by positivity
  have hc' : c ≠ 0 := hc.ne'
  have hM' : M ≠ 0 := hM.ne'
  have hcB : 0 ≤ c * B := by positivity
  calc c * P⁻¹ * B = (c * B) / P := by ring
    _ ≤ (c * B) / (16 * c * M) := div_le_div_of_nonneg_left hcB hP0 hP
    _ = B / M / 2 / 8 := by field_simp; ring
end Formalism.CountingSumsFrames
