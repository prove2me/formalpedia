-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.dual2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:51:24.30941+00:00
-- url     : https://prove2.me/submissions/7f2480b5-54b2-4aaa-933c-9c83ba696145

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_dual1
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
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
variable {ι : Type}
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution [Fintype ι] [DecidableEq ι] (hd : Even d) (σ : K →+* K) {om oms : ι → K}
    (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (hT : TrDual d σ om oms)
    (s s' : ZMod d) :
    (∑ x : Bool × ι, mXY σ om oms s x * pXY σ om oms x s') = if s = s' then 1 else 0 := by
  have hcard : Fintype.card (Bool × ι) = Fintype.card (ZMod d) := by
    rw [Fintype.card_prod, Fintype.card_bool, ZMod.card, hT.1]
  obtain ⟨e⟩ : Nonempty (Bool × ι ≃ ZMod d) := ⟨Fintype.equivOfCardEq hcard⟩
  have hAB : (Matrix.of fun (i s : ZMod d) => pXY σ om oms (e.symm i) s) *
      (Matrix.of fun (s j : ZMod d) => mXY σ om oms s (e.symm j)) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [dual1 hd σ hfix hT]
    simp only [e.symm.injective.eq_iff]
  have h2 := congrArg (fun M => M s s') (mul_eq_one_comm.1 hAB)
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h2
  rw [← h2]
  exact Fintype.sum_equiv e _ _ (fun x => by simp)
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
