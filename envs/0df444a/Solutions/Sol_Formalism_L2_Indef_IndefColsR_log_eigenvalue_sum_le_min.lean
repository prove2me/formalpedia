-- Prove2me | solution 1 for Formalism.L2.Indef.IndefColsR.log_eigenvalue_sum_le_min
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:00.245154+00:00
-- url     : https://prove2.me/submissions/a8f48a6d-675d-4b37-90ca-68d11cf4a647

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Indef.IndefColsR
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
  (S : IndefColsR Df Dc Sp N)
namespace Formalism.L2.Indef.IndefColsR
theorem _root_.solution [Nonempty Bs.Ix] (v : InfinitePlace K) :
    ∑ j, N.l6 j ≤ minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) :=
  Finset.le_inf' _ _ fun p _ => Finset.sum_le_sum fun j _ => S.l6 j p v
end Formalism.L2.Indef.IndefColsR
