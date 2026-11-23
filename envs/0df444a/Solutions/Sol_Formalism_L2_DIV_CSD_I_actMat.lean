-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.I_actMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:59.186088+00:00
-- url     : https://prove2.me/submissions/5851d041-666c-4713-b53c-2c912dc00d1d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas

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
open Formalism.L2.DIV.CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution (t : G) (x : Fin S.dim → K) :
    S.I ((S.actMat r t).mulVec x) = (r t (S.basis.equivFun.symm x) : S.Cl → S.V) := by
  show ((S.basis.equivFun.symm ((S.actMat r t).mulVec x) : S.Forms) : S.Cl → S.V) = _
  congr 1
  apply S.basis.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, Basis.equivFun_apply,
    ← LinearMap.toMatrix_mulVec_repr S.basis S.basis, ← Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]
  rfl
end Formalism.L2.DIV.CSD
