-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.actMat_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:33.461841+00:00
-- url     : https://prove2.me/submissions/cfd0e191-3436-4823-a94a-e558461c1ebd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_actMat_unitary
import Theorems.Thm_Formalism_L2_DIV_CSD_actMat_mul_inv

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
theorem _root_.solution (hr : S.ActGood r) (t : G) :
    (S.actMat r t)ᴴ * S.H = S.H * S.actMat r t⁻¹ := by
  calc (S.actMat r t)ᴴ * S.H = (S.actMat r t)ᴴ * S.H * (S.actMat r t * S.actMat r t⁻¹) := by
        rw [S.actMat_mul_inv r t, Matrix.mul_one]
    _ = ((S.actMat r t)ᴴ * S.H * S.actMat r t) * S.actMat r t⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = S.H * S.actMat r t⁻¹ := by rw [S.actMat_unitary r hr t]
end Formalism.L2.DIV.CSD
