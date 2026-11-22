-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sizeBound_multiplicity_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:42.313896+00:00
-- url     : https://prove2.me/submissions/a23956a5-0b0a-470e-b5c1-a214a3f318ee

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds

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
theorem _root_.solution (r k Q c' al : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hk8 : 8 ≤ k) (hc : 1 ≤ c')
    (hal : al ≤ 1 + r * k * Q) :
    (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' ≤ 3 * r * k * c' * Q := by
  have hrk : 16 ≤ r * k := by nlinarith
  have e1 : c' * al ≤ c' * (1 + r * k * Q) := mul_le_mul_of_nonneg_left hal (by linarith)
  have hcQ : 1 ≤ c' * Q := by nlinarith
  have e2 : k * Q ≤ k * (c' * Q) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have e3 : 2 * k * (c' * Q) ≤ r * k * (c' * Q) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  have e4 : 16 * (c' * Q) ≤ r * k * (c' * Q) := by nlinarith
  have e5 : c' ≤ c' * Q := by nlinarith
  nlinarith
end Formalism.CountingSumsFrames
