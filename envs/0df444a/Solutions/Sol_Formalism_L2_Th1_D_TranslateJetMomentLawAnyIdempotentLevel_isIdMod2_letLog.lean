-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.isIdMod2_letLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:30.242859+00:00
-- url     : https://prove2.me/submissions/4811188f-5c4e-4498-8ad6-08854968b608

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_letLog_eq
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_coeff_one_gLog
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
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution [CharZero K] {l d : ℕ} [NeZero d] (hl : l.Prime) :
    Formalism.FG.IsIdMod2 (letLog (K := K) (d := d) l) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show (∑ e ∈ Finset.range ((0 : ZMod d →₀ ℕ).degree + 1),
      if (0 : ZMod d →₀ ℕ) = Finsupp.single (j - 2 * (e : ZMod d)) ((l ^ 2) ^ e) then
        ((l : K) ^ e)⁻¹ else 0) = 0
    exact Finset.sum_eq_zero fun e _ =>
      if_neg (Finsupp.single_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hl.ne_zero))).symm
  · rw [letLog_eq, coeff_one_gLog hl]
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
