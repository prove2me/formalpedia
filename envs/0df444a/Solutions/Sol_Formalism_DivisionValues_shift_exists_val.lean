-- Prove2me | solution 1 for Formalism.DivisionValues.shift_exists_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:28.151799+00:00
-- url     : https://prove2.me/submissions/b32d5d40-1501-48cb-8a43-07c9a030c714

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
import Theorems.Thm_Formalism_DivisionValues_shift_vw_pow
import Theorems.Thm_Formalism_DivisionValues_shift_coe_ne_zero
import Theorems.Thm_Formalism_DivisionValues_shift_decomp
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties


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
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (s : ℤ) : ∃ a : K, a ≠ 0 ∧ vw w a = s := by
  obtain ⟨ϖ, hϖ0, hϖ1, -⟩ := shift_decomp w
  have hϖ : (ϖ : K) ≠ 0 := shift_coe_ne_zero hϖ0
  rcases Int.eq_nat_or_neg s with ⟨n, rfl | rfl⟩
  · refine ⟨(ϖ : K) ^ n, pow_ne_zero n hϖ, ?_⟩
    rw [shift_vw_pow w _ hϖ, hϖ1, mul_one]
  · refine ⟨((ϖ : K) ^ n)⁻¹, inv_ne_zero (pow_ne_zero n hϖ), ?_⟩
    rw [(valuation_basic_properties K w).2.2.2.2.2.1, shift_vw_pow w _ hϖ, hϖ1, mul_one]
end Formalism.DivisionValues
