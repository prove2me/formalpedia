-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.geomSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:47.525093+00:00
-- url     : https://prove2.me/submissions/8dc33e7d-8fde-42fd-8ddd-8f1f346b8005

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A_geom_sum_mul_pred

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
theorem _root_.solution : GeomSum := by
  intro c x R hc hx0 hx
  set K := Real.exp 1 * √c with hK
  have hK0 : 0 ≤ K := by positivity
  have hden : 0 < 2 * (1 + 2 * Real.exp 1 * √c) := by positivity
  have hx2 : x ≤ 1 / 2 := by
    refine le_trans hx ?_
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  have h1 := geom_sum_mul_pred x hx0 hx2 R
  have h2 : 0 ≤ x ^ (R + 1) := by positivity
  have h3 : ∑ p ∈ Icc 1 R, x ^ p ≤ 2 * x := by linarith
  rw [← Finset.mul_sum]
  have h4 : x * (2 * (1 + 2 * K)) ≤ 1 := by
    have := hx
    rw [le_div_iff₀ hden] at this
    simpa [hK, mul_assoc] using this
  calc K * ∑ p ∈ Icc 1 R, x ^ p ≤ K * (2 * x) := mul_le_mul_of_nonneg_left h3 hK0
    _ ≤ 1 / 2 := by nlinarith
end Formalism.FourierDecayAlt.P.LEx2.A
