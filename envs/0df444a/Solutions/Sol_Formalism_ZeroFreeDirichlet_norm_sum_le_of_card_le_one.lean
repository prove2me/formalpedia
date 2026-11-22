-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_sum_le_of_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:44.943119+00:00
-- url     : https://prove2.me/submissions/8fb20c43-9041-42c4-a727-f517641cfe67

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (B : Finset ℝ) (hB : B.card ≤ 1) (f : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ β ∈ B, ‖f β‖ ≤ M) : ‖∑ β ∈ B, f β‖ ≤ M := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hB with h | h
  · rw [Finset.card_eq_zero.mp h]; simpa using hM
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp h
    simpa using hf b (Finset.mem_singleton_self b)
end Formalism.ZeroFreeDirichlet
