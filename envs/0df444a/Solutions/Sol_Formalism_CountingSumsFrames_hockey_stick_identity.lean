-- Prove2me | solution 1 for Formalism.CountingSumsFrames.hockey_stick_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:51.880835+00:00
-- url     : https://prove2.me/submissions/95322994-efa6-41fa-87eb-a0982ea87bab

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity

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
theorem _root_.solution : HockeyStick := by
  intro m B
  induction B with
  | zero => simp [dimPol]
  | succ B ih =>
    rw [Finset.sum_range_succ']
    have h1 : ∀ j ∈ range (B + 1), dimPol m (B + 1 - (j + 1)) = dimPol m (B - j) := by
      intro j _
      congr 1
      omega
    rw [Finset.sum_congr rfl h1, ih]
    simp only [dimPol, Nat.sub_zero]
    have : B + 1 + (m + 1) = (B + m + 1) + 1 := by ring
    rw [this, Nat.choose_succ_succ]
    have h2 : B + 1 + m = B + m + 1 := by ring
    have h3 : B + (m + 1) = B + m + 1 := by ring
    rw [h2, h3, add_comm]
end Formalism.CountingSumsFrames
