-- Prove2me | solution 1 for Formalism.BehrendSets.Sums.linB_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:43.808245+00:00
-- url     : https://prove2.me/submissions/64653fc1-fa61-4840-9859-554966691917

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoLeCastOfTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Sums
namespace Formalism.BehrendSets.Sums
theorem _root_.solution (m K L : ℝ) (hm : 2 ≤ m) (hK : 1 ≤ K) (hL : 0 ≤ L) :
    L / (m * K - 1) ≤ 2 * L * (1 / K) / m := by
  have hm0 : m ≠ 0 := by positivity
  have hK0 : K ≠ 0 := by positivity
  have hx : 2 ≤ m * K := by nlinarith
  calc L / (m * K - 1) ≤ L / (m * K / 2) :=
        div_le_div_of_nonneg_left hL (by positivity) (by linarith)
    _ = 2 * L * (1 / K) / m := by
        field_simp
end Formalism.BehrendSets.Sums
