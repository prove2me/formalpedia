-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.geom_sum_mul_pred
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:32.884803+00:00
-- url     : https://prove2.me/submissions/24bd8c7e-ae0f-4513-9c97-f22a17a86b9c

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx2.A
theorem _root_.solution (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1/2) (R : ℕ) : ∑ p ∈ Icc 1 R, x ^ p ≤ 2 * x - 2 * x ^ (R + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 : 0 ≤ x ^ (R + 1) := by positivity
    have h2 : x ^ (R + 1 + 1) = x ^ (R + 1) * x := pow_succ _ _
    nlinarith
end Formalism.FourierDecayAlt.P.LEx2.A
