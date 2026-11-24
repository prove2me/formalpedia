-- Prove2me | solution 1 for Formalism.L2.Col.LocOp.ker_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:49.15727+00:00
-- url     : https://prove2.me/submissions/7cce1a72-79ec-4893-9312-747b84a56aff

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

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
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.LocOp
variable {S S' : GSD K}
namespace Formalism.L2.Col.LocOp
theorem _root_.solution (A : LocOp S S') (B : LocOp S' S) (hn : S.pair.Nondegenerate)
    (hn' : S'.pair.Nondegenerate)
    (hadj : ∀ d d' x y, S'.pair (A.ker d' d x) y = S.pair x (B.ker d d' y)) (d : S.D) (d' : S'.D) :
    A.ker d' d = 0 ↔ B.ker d d' = 0 := by
  constructor
  · intro hA
    ext y
    rw [LinearMap.zero_apply]
    refine hn.2 _ fun x => ?_
    rw [← hadj, hA, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
  · intro hB
    ext x
    rw [LinearMap.zero_apply]
    refine hn'.1 _ fun y => ?_
    rw [hadj, hB, LinearMap.zero_apply, map_zero]
end Formalism.L2.Col.LocOp
