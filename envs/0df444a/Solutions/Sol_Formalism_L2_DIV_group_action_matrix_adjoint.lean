-- Prove2me | solution 1 for Formalism.L2.DIV.group_action_matrix_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:50.610737+00:00
-- url     : https://prove2.me/submissions/ae2ace16-d1ba-48f9-a6d2-cdf65383fff8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_gaMat_eq_lift
import Theorems.Thm_Formalism_L2_DIV_CSD_actMat_adj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : GaMatAdj := by
  intro K _ _ _ S G _ _ r hr a
  rw [S.gaMat_eq_lift r (gaStar a)]
  unfold gaStar
  rw [map_sum]
  simp only [MonoidAlgebra.lift_single]
  unfold CSD.gaMat
  rw [Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, S.actMat_adj r hr t, Matrix.mul_smul]
  rfl
end Formalism.L2.DIV
