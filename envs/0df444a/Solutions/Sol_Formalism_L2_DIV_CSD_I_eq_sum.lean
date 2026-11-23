-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.I_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:14.9842+00:00
-- url     : https://prove2.me/submissions/c34efc0f-c9b5-4df1-b801-0cca6463553b

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_I_apply

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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution (x : Fin S.dim → K) : S.I x = ∑ i, x i • (S.basis i : S.Cl → S.V) := by
  rw [I_apply, Basis.equivFun_symm_apply]
  simp
end Formalism.L2.DIV.CSD
