-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.zXY_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:40:25.723679+00:00
-- url     : https://prove2.me/submissions/92f72148-ecdb-46ac-9fa3-33975f9b91dd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_zXY_eq
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_artin_hasse_log_frobenius_shift
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_mXY_shift
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
variable {K : Type} [Field K] {d : ℕ} [NeZero d] {ι : Type}
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution [CharZero K] [Fintype ι] {l : ℕ} (hl : l.Prime) (hd : Even d) (σ : K →+* K)
    {om oms : ι → K} (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (s : ZMod d) :
    zXY l σ om oms s -
        C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (zXY l σ om oms (s - 2))) =
      ∑ x : Bool × ι, C (mXY σ om oms s x) * X x := by
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hA : ∀ x : Bool × ι, at1 x (lgF K l) -
      C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (at1 x (lgF K l))) = X x :=
    fun x => artin_hasse_log_frobenius_shift hl (σ.comp σ) x
  simp only [frobVar_eq_expand hq] at hA ⊢
  rw [zXY_eq l σ om oms s, zXY_eq l σ om oms (s - 2)]
  simp only [map_sum, map_mul, MvPowerSeries.map_C, RingHom.coe_comp, Function.comp_apply,
    mXY_shift hd σ hfix, MvPowerSeries.expand_C]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hA x]
  ring
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
