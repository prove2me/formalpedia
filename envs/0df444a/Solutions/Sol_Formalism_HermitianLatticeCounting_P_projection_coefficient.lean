-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.projection_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:41.649898+00:00
-- url     : https://prove2.me/submissions/41bbb2ef-4129-4536-a3cf-c84c4cb0197d

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ProjCoeff := by
  intro G H _ _ U P m hP hPU v hv hn g
  have h1 := congrArg (fun T : H →L[ℂ] H => T v) (hPU g)
  simp only [ContinuousLinearMap.comp_apply, hv, _root_.smul_apply] at h1
  calc inner ℂ v (U g v) = inner ℂ (P v) (U g v) := by rw [hv]
    _ = inner ℂ v (P (U g v)) := hP _ _
    _ = inner ℂ v (m g • v) := by rw [h1]
    _ = m g := by rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hn]; simp
end Formalism.HermitianLatticeCounting.P
