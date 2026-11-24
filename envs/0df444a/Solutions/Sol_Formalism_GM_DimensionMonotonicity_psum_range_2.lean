-- Prove2me | solution 2 for Formalism.GM.DimensionMonotonicity.psum_range
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-23T22:51:39.455905+00:00
-- url     : https://prove2.me/submissions/214e2d0a-3128-4bbc-b32d-d61cc8c49a8d

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
variable {r : ℕ}

theorem solution (g : ℕ → ℤ) {k r : ℕ} (h : k ≤ r) :
    ∑ c ∈ range r, (if c < k then g c else 0) = ∑ c ∈ range k, g c := by
  induction r, h using Nat.le_induction with
  | base => exact Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))
  | succ n hn ih => rw [Finset.sum_range_succ, if_neg (Nat.not_lt.mpr hn), add_zero, ih]
