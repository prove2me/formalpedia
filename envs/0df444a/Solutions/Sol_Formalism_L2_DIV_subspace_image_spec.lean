-- Prove2me | solution 1 for Formalism.L2.DIV.subspace_image_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:36.785807+00:00
-- url     : https://prove2.me/submissions/e19c193d-b6ca-4cf9-be26-a57b556410f9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_subE_mulVec

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
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution : SubESpec := by
  intro K _ _ n Z
  constructor
  · intro x y hxy
    rw [subE_mulVec, subE_mulVec] at hxy
    exact (subBasis Z).equivFun.symm.injective (Subtype.ext hxy)
  · ext v
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, subE_mulVec]
    constructor
    · rintro ⟨x, rfl⟩
      exact ((subBasis Z).equivFun.symm x).2
    · intro hv
      exact ⟨(subBasis Z).equivFun ⟨v, hv⟩, by simp⟩
end Formalism.L2.DIV
