-- Prove2me | solution 1 for Formalism.L2.Th1.G.jetsIn_subst_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:02.125577+00:00
-- url     : https://prove2.me/submissions/3748cb3d-1672-4208-a457-b4e2c7c44a9c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_divPow
import Theorems.Thm_Formalism_L2_Th1_G_coeff_subst_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single


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
theorem _root_.solution {f : PowerSeries K} {a : MvPowerSeries ι K} (hf : JetsIn1 R f)
    (h0 : MvPowerSeries.constantCoeff a = 0) (ha : JetsIn R a) :
    JetsIn R (PowerSeries.subst a f) := by
  intro n
  rw [coeff_subst_one f h0 (Nat.lt_succ_self n.degree), Finset.mul_sum]
  refine sum_mem (fun k _ => ?_)
  have hk : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have e : ((mfact n : ℕ) : K) * (PowerSeries.coeff k f * MvPowerSeries.coeff n (a ^ k)) =
      (((k.factorial : ℕ) : K) * PowerSeries.coeff k f) *
        (((mfact n : ℕ) : K) *
          MvPowerSeries.coeff n (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k)) := by
    rw [MvPowerSeries.coeff_C_mul]
    calc _ = (((mfact n : ℕ) : K) * (PowerSeries.coeff k f * MvPowerSeries.coeff n (a ^ k))) *
          (((k.factorial : ℕ) : K) * ((k.factorial : K))⁻¹) := by rw [mul_inv_cancel₀ hk, mul_one]
      _ = _ := by ring
  rw [e]
  exact R.mul_mem (hf k) (jetsIn_divPow h0 ha k n)
end Formalism.L2.Th1.G
