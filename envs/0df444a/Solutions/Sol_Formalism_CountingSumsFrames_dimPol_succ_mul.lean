-- Prove2me | solution 1 for Formalism.CountingSumsFrames.dimPol_succ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:22.17872+00:00
-- url     : https://prove2.me/submissions/af90e192-b844-4a76-8749-6183acfdc417

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (r x : ℕ) :
    ((r : ℝ) + 1) * dimPol (r + 1) x = ((x : ℝ) + r + 1) * dimPol r x := by
  unfold dimPol
  have h := Nat.add_one_mul_choose_eq (x + r) r
  have h2 := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h2
  rw [show x + (r + 1) = x + r + 1 from rfl]
  linarith
end Formalism.CountingSumsFrames
