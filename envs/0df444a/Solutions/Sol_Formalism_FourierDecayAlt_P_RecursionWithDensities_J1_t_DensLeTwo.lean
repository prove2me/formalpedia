-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.J1.t_DensLeTwo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:03.106273+00:00
-- url     : https://prove2.me/submissions/a95d5492-e6c9-4f44-8ce8-95b7865d7809

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
theorem _root_.solution : DensLeTwo := by
  intro f n h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have h' : (18 : ℝ) * f ≤ 2 ^ n := by exact_mod_cast h
  have hy : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hpos
  have hy1 : ((2 : ℝ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have hm := mul_le_mul_of_nonneg_left h' hy.le
  have hx : 12 * (f : ℝ) * ((2 : ℝ) ^ n)⁻¹ ≤ 2 / 3 := by nlinarith
  have hl := Real.log_two_gt_d9
  have h3 : Real.exp (12 * (f : ℝ) * ((2 : ℝ) ^ n)⁻¹) ≤ Real.exp (Real.log 2) :=
    Real.exp_le_exp.mpr (by linarith)
  rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h3
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
