-- Prove2me | solution 1 for Formalism.L2.DIV.idemOfSpec_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:22:02.422039+00:00
-- url     : https://prove2.me/submissions/0d94942a-3afa-4d13-b603-a60eeb4d768b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_gaStar_sum
import Theorems.Thm_Formalism_L2_DIV_idemOf_central
import Theorems.Thm_Formalism_L2_DIV_coeff_idemOf
import Theorems.Thm_Formalism_L2_DIV_idemOf_integral
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_mem_cmMax
import Theorems.Thm_Formalism_L2_DIV_chiIdem_selfAdj

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
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
theorem _root_.solution
    (hidem : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)),
      (∀ χ ∈ X, IsAbsIrrChar χ) → idemOf X * idemOf X = idemOf X) : IdemOfSpec := by
  intro K _ _ _ v0 hv G _ _ X hX
  refine ⟨⟨hidem K G X hX, ?_, ?_, idemOf_integral X hX⟩, idemOf_central X hX⟩
  · unfold idemOf
    rw [gaStar_sum]
    exact Finset.sum_congr rfl fun χ hχ => chiIdem_selfAdj hv (hX χ hχ)
  · intro t
    rw [coeff_idemOf]
    exact sum_mem fun χ hχ => mul_mem (div_mem ((hX χ hχ).mem_cmMax hv 1) (natCast_mem _ _))
      ((hX χ hχ).mem_cmMax hv t⁻¹)
end Formalism.L2.DIV
