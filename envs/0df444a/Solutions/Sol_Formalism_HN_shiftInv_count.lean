-- Prove2me | solution 1 for Formalism.HN.shiftInv_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:29.478691+00:00
-- url     : https://prove2.me/submissions/a184c728-edc2-4e45-829a-7eae4108f8b3

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w w₂
namespace Formalism.HN
theorem _root_.solution (c : ℝ) (k m : ℕ) :
    (∑ i ∈ Finset.range m, if i < k then c else 0) = c * ((min k m : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : m < k
    · rw [if_pos h, min_eq_right h.le, min_eq_right (show m + 1 ≤ k by omega)]
      push_cast
      ring
    · rw [if_neg h]
      replace h := not_lt.mp h
      rw [min_eq_left h, min_eq_left (show k ≤ m + 1 by omega)]
      ring
end Formalism.HN
