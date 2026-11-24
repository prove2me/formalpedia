-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.funEq_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:37:44.695145+00:00
-- url     : https://prove2.me/submissions/c0953352-d538-469b-bf29-a1d0e6ca596b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
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
theorem _root_.solution {l : ℕ} (hq : l ^ 2 ≠ 0) (σ : K →+* K) {τ : Type}
    {L : ZMod d → MvPowerSeries τ K} (hL : ShiftType l σ L) :
    Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (sM K d) L := by
  intro j
  have h := (hL j).2
  rw [frobVar_eq_expand hq, ← MvPowerSeries.smul_eq_C_mul] at h
  have hsum : (∑ k, sM K d j k • MvPowerSeries.expand (l ^ 2) hq (MvPowerSeries.map (σ.comp σ) (L k))) =
      MvPowerSeries.expand (l ^ 2) hq (MvPowerSeries.map (σ.comp σ) (L (j - 2))) := by
    simp [sM, ite_smul, Finset.sum_ite_eq']
  rw [hsum]
  exact h
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
