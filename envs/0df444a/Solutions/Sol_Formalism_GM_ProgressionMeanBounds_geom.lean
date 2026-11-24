-- Prove2me | solution 1 for Formalism.GM.ProgressionMeanBounds.geom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:43.429643+00:00
-- url     : https://prove2.me/submissions/5e55936d-194b-4e2f-8755-56e37c232c08

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Formalism.GM.ProgressionMeanBounds
open Finset Polynomial
namespace Formalism.GM.ProgressionMeanBounds
theorem _root_.solution (p : ℝ) (hp : 2 ≤ p) (h : ℕ) :
    ∑ i ∈ Icc 1 h, (1 : ℝ) / p ^ i = (1 - 1 / p ^ h) / (p - 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    field_simp
    ring
end Formalism.GM.ProgressionMeanBounds
