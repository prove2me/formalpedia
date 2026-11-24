-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.shiftType_zXY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:29.6008+00:00
-- url     : https://prove2.me/submissions/6403d715-5f6e-44a5-b699-8eb0f9a3997d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_cc_zXY
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_zXY_shift
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_norm_mXY
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries
open Pair TranslateJetMomentLawAnyIdempotentLevel
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [NormedField K] {d : ℕ} [NeZero d] {ι : Type}
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution [IsUltrametricDist K] [CharZero K] [Fintype ι] {l : ℕ} (hl : l.Prime)
    (hd : Even d) {σ : K →+* K} (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) {om oms : ι → K}
    (hO : OwOK d σ om oms) : ShiftType l σ (zXY (d := d) l σ om oms) := by
  classical
  intro s
  refine ⟨cc_zXY hl.two_le σ om oms s, ?_⟩
  rw [zXY_shift hl hd σ hO.2 s]
  intro n
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, norm_mul]
  split_ifs <;> simp [norm_mXY hσ hO.1 s x]
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
