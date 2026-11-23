-- Prove2me | solution 1 for Formalism.L2.DIV.gaMat_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:16.245783+00:00
-- url     : https://prove2.me/submissions/778cc41b-d429-4700-a552-204cd51fff73

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
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G]
    [Fintype G] (r : Representation K G S.Forms) (hr : S.ActRat r) (a : MonoidAlgebra K G)
    (ha : ∀ t, a.coeff t ∈ cmMax K) (i j : Fin S.dim) : S.gaMat r a i j ∈ cmMax K := by
  unfold CSD.gaMat
  rw [Matrix.sum_apply]
  exact sum_mem fun t _ => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (ha t) (hr t i j)
end Formalism.L2.DIV
