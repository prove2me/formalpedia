-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.coeff_subst_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:33:42.797221+00:00
-- url     : https://prove2.me/submissions/25d50588-8a28-4110-8ee9-0bc5d9810c2b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_coeff_pow_zero
import Theorems.Thm_Formalism_L2_Th1_C_Pts_hasSubst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.Th1.C.Clo
theorem _root_.solution {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (g : PowerSeries K) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff n (PowerSeries.subst f g) =
      ∑ k ∈ range (n.degree + 1), PowerSeries.coeff k g * MvPowerSeries.coeff n (f ^ k) := by
  classical
  rw [PowerSeries.coeff_subst (Pts.hasSubst hf),
    finsum_eq_sum_of_support_subset (s := range (n.degree + 1))]
  · exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul]
  · intro k hk
    simp only [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hk
    rw [coeff_pow_zero hf (by omega), smul_zero]
end Formalism.L2.Th1.C.Clo
