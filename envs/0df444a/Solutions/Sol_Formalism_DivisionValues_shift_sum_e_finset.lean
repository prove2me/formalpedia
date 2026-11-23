-- Prove2me | solution 1 for Formalism.DivisionValues.shift_sum_e_finset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:11.284851+00:00
-- url     : https://prove2.me/submissions/bd4a7a29-87a3-492b-8f39-dd9cae1717ac

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_DivisionValues_shift_above_iff
import Theorems.Thm_Formalism_DivisionValues_shift_vw_nat_nonneg
import Theorems.Thm_Formalism_DivisionValues_shift_sum_e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable [IsTotallyComplex K]
namespace Formalism.DivisionValues
theorem _root_.solution (p : ℕ) (hp : p.Prime) :
    ∑ w ∈ (shift_above_finite (K := K) p hp).toFinset, lw w * (vw w (p : K) : ℝ) = Real.log p := by
  rw [← (shift_sum_e (K := K) p hp).2]
  symm
  apply finsum_eq_sum_of_support_subset
  intro w hw
  simp only [Function.mem_support, ne_eq] at hw
  rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq, shift_above_iff p hp]
  have h1 : (vw w (p : K) : ℝ) ≠ 0 := right_ne_zero_of_mul hw
  have h2 : vw w (p : K) ≠ 0 := by exact_mod_cast h1
  have h3 := shift_vw_nat_nonneg (K := K) p w
  omega
end Formalism.DivisionValues
