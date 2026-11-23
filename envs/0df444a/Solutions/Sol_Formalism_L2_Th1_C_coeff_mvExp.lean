-- Prove2me | solution 1 for Formalism.L2.Th1.C.coeff_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:57.095423+00:00
-- url     : https://prove2.me/submissions/ae0d9473-9115-4429-8b83-e917514c1e44

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_hasSubst_of_cc
import Theorems.Thm_Formalism_L2_Th1_C_coeff_pow_eq_zero_of_cc

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
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C
theorem _root_.solution {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    {n : σ →₀ ℕ} {N : ℕ} (hN : n.degree < N) :
    MvPowerSeries.coeff n (mvExp f) =
      ∑ k ∈ range N, ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ k) := by
  classical
  unfold mvExp
  rw [PowerSeries.coeff_subst (hasSubst_of_cc hf),
    finsum_eq_sum_of_support_subset _ (s := Finset.range N) ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [PowerSeries.coeff_exp]
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hkN
    apply hk
    simp [coeff_pow_eq_zero_of_cc hf (show n.degree < k by omega)]
end Formalism.L2.Th1.C
