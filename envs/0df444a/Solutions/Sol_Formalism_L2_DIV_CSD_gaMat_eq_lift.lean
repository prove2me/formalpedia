-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.gaMat_eq_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:59.211469+00:00
-- url     : https://prove2.me/submissions/ab29ac32-fb94-4c45-b02a-91b0f215856e

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
theorem _root_.solution (a : MonoidAlgebra K G) :
    S.gaMat r a = MonoidAlgebra.lift K (Matrix (Fin S.dim) (Fin S.dim) K) G (S.actHom r) a := by
  rw [MonoidAlgebra.lift_apply]
  unfold CSD.gaMat
  rw [Finsupp.sum_fintype]
  · rfl
  · intro
    exact zero_smul _ _
end Formalism.L2.DIV.CSD
