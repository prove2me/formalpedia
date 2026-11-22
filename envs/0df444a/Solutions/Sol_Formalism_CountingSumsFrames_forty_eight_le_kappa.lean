-- Prove2me | solution 1 for Formalism.CountingSumsFrames.forty_eight_le_kappa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:12.151616+00:00
-- url     : https://prove2.me/submissions/4aa5df21-a755-4589-a9bb-404db58b1877

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp

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
theorem _root_.solution {p r s : ℕ} {a : ℝ} (hr : (2:ℝ) ≤ r) (hlg : 2 < lgSeg p a r) : 48 ≤ kapSeg p a r s := by
  unfold kapSeg
  have hs2 : (2:ℝ) ≤ (s:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) s; linarith
  have hlg' := hlg.le
  calc (48:ℝ) = 3*2*2^2*2 := by norm_num
    _ ≤ 3 * ((s : ℝ) + 2) * (r : ℝ) ^ 2 * lgSeg p a r := by gcongr
end Formalism.CountingSumsFrames
