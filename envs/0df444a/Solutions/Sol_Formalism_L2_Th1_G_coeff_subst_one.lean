-- Prove2me | solution 1 for Formalism.L2.Th1.G.coeff_subst_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:47:16.609587+00:00
-- url     : https://prove2.me/submissions/6c10a3b0-ce19-447b-89ff-5d707a5e9991

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single
import Theorems.Thm_Formalism_L2_Th1_C_coeff_pow_eq_zero_of_cc
import Theorems.Thm_Formalism_L2_Th1_C_hasSubst_of_cc


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral mfact_add_single)
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {ι : Type}
namespace Formalism.L2.Th1.G
theorem _root_.solution (f : PowerSeries K) {a : MvPowerSeries ι K}
    (h0 : MvPowerSeries.constantCoeff a = 0) {n : ι →₀ ℕ} {N : ℕ} (hN : n.degree < N) :
    MvPowerSeries.coeff n (PowerSeries.subst a f) =
      ∑ k ∈ range N, PowerSeries.coeff k f * MvPowerSeries.coeff n (a ^ k) := by
  classical
  rw [PowerSeries.coeff_subst (Formalism.L2.Th1.C.hasSubst_of_cc h0),
    finsum_eq_sum_of_support_subset (s := range N)]
  · exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul]
  · intro k hk
    simp only [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hk
    rw [Formalism.L2.Th1.C.coeff_pow_eq_zero_of_cc h0 (by omega), smul_zero]
end Formalism.L2.Th1.G
