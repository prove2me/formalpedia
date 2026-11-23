-- Prove2me | solution 1 for Formalism.DivisionValues.lattice_weight_sum_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:33.028924+00:00
-- url     : https://prove2.me/submissions/3b06e6f4-a9f5-4736-a691-27adbb3ce50c

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
import Theorems.Thm_Formalism_DivisionValues_shift_lw_pos
import Theorems.Thm_Formalism_DivisionValues_shift_above_iff
import Theorems.Thm_Formalism_DivisionValues_shift_vw_nat_nonneg
import Theorems.Thm_Formalism_DivisionValues_shift_sum_e
import Theorems.Thm_Formalism_DivisionValues_shift_sum_e_finset
import Theorems.Thm_Formalism_DivisionValues_shift_sum_above
import Theorems.Thm_Formalism_DivisionValues_shift_sum_above_le

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
namespace Formalism.DivisionValues
theorem _root_.solution : LwSumPrime := by
  intro K _ _ _ _ p hp
  have hsum := shift_sum_e (K := K) p hp
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hex : ∃ w : HeightOneSpectrum (𝓞 K), Above p w := by
    by_contra hno
    push_neg at hno
    have h0 : ∀ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (p : K) : ℝ) = 0 := by
      intro w
      have h1 : ¬ 0 < vw w (p : K) := fun h => hno w ((shift_above_iff p hp w).2 h)
      have h3 := shift_vw_nat_nonneg (K := K) p w
      have h2 : vw w (p : K) = 0 := by omega
      rw [h2]
      simp
    have h4 := hsum.2
    rw [finsum_congr h0, finsum_zero] at h4
    linarith
  refine ⟨shift_above_finite (K := K) p hp, hex, fun w => shift_above_iff p hp w,
    fun w => shift_lw_pos w, hsum.2, shift_sum_above_le (K := K) p hp, ?_⟩
  intro e he
  have he0 : (0 : ℝ) < e := by
    obtain ⟨w0, hw0⟩ := hex
    have h5 := (shift_above_iff p hp w0).1 hw0
    rw [he w0 hw0] at h5
    exact_mod_cast h5
  rw [eq_div_iff he0.ne', shift_sum_above (K := K) p hp, Finset.sum_mul,
    ← shift_sum_e_finset (K := K) p hp]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Set.Finite.mem_toFinset] at hw
  rw [he w hw]
end Formalism.DivisionValues
