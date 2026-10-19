-- Prove2me | solution 1 for CohnElkies.lower_integer_leftRiemann_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/7b3a1c07-c5e9-4e78-9695-9c6f9c9bbf3a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerRiemannLog_monotoneOn
import Theorems.Thm_CohnElkies_monotone_leftRiemann_error

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {T : ℝ} (hT : T ≠ 0) {k : ℕ} (hk : 0 < k) :
    0 ≤
        (k : ℝ) * (∫ x in (0 : ℝ)..1, lowerRiemannLog T x) -
          ∑ j ∈ Finset.range k,
            lowerRiemannLog T ((j : ℝ) / (k : ℝ)) ∧
      (k : ℝ) * (∫ x in (0 : ℝ)..1, lowerRiemannLog T x) -
          ∑ j ∈ Finset.range k,
            lowerRiemannLog T ((j : ℝ) / (k : ℝ)) ≤
        lowerRiemannLog T 1 - lowerRiemannLog T 0 := by
  exact monotone_leftRiemann_error (lowerRiemannLog T) hk
    ((lowerRiemannLog_monotoneOn hT).mono (by intro x hx; exact hx.1))
end CohnElkies
