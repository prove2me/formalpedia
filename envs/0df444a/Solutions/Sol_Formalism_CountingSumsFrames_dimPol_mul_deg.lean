-- Prove2me | solution 1 for Formalism.CountingSumsFrames.dimPol_mul_deg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:40.369581+00:00
-- url     : https://prove2.me/submissions/28d7faf3-bce5-4837-9bfd-aadf2aceb4b7

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec

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
theorem _root_.solution (k' b : ℕ) : dimPol k' b * (b + 1 + k') = dimPol k' (b + 1) * (b + 1) := by
  unfold dimPol
  have h := Nat.choose_mul_succ_eq (b + k') k'
  rw [show b + k' + 1 - k' = b + 1 by omega] at h
  rw [show b + 1 + k' = b + k' + 1 by omega]
  exact h
end Formalism.CountingSumsFrames
