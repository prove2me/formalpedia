-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.csum_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:55.2333+00:00
-- url     : https://prove2.me/submissions/a701bc17-7276-4d3f-8c85-37dd82d82ba6

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_I_eq_sum

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
theorem _root_.solution (x y : Fin S.dim → K) :
    S.csum (S.I x) (S.I y) = ∑ i, ∑ j, star (x i) * S.H i j * y j := by
  simp only [csum, I_eq_sum, H, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, map_sum,
    LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
end Formalism.L2.DIV.CSD
