-- Prove2me | solution 1 for Formalism.CountingSumsFrames.fock_L_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:02.090032+00:00
-- url     : https://prove2.me/submissions/548b1bf4-4320-4641-8b01-e9d26b510310

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds

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
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (a : ℝ) (ha : 0 ≤ a) (hk : 1 ≤ k) :
    0 ≤ Real.logb p (2 * a + k) + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hx : (1 : ℝ) ≤ 2 * a + k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have := Real.logb_nonneg hp1 hx
  linarith
end Formalism.CountingSumsFrames
