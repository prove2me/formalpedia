-- Prove2me | solution 1 for Formalism.L2.Th1.D.OneLetterHalf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:32:35.834779+00:00
-- url     : https://prove2.me/submissions/beab6af0-4a35-4499-b1a2-da7e3c48a35a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_AtVariableArtinHasseEqOneLog
import Theorems.Thm_Formalism_L2_Th1_D_SingleLetterLog_linEL_two
import Theorems.Thm_Formalism_L2_Th1_D_SingleLetterLog_linOL_two
import Theorems.Thm_Formalism_L2_Th1_D_SingleLetterLog_trDual_two
import Theorems.Thm_Formalism_L2_Th1_D_SingleLetterLog_owOK_two
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_simeqRules
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_lamModule
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_simeqRules
import Theorems.Thm_Formalism_L2_Th1_D_B4_simeq_sub_zero
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_ip_lgF
import Theorems.Thm_Formalism_L2_Th1_D_Pair_addC_log
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_lgF
import Theorems.Thm_Formalism_L2_Th1_D_exponential_specification
import Theorems.Thm_Formalism_L2_Th1_D_subst_tilde


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus oneLog thetaOne)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open SingleLetterLog Pair
namespace Formalism.L2.Th1.D
theorem _root_.solution : MeanSimeqL → OneLetterHalf := by
  intro hM K0 _ _ _ l σ hU F hF be0 hF1 hF2 ζ hζ ph hph
  have hp : l.Prime := hU.1
  have hl : 2 ≤ l := hp.two_le
  have hlK : (l : K0) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hrefl, hsymm, htrans, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules K0 Unit
  have hST : ShiftType l σ (fun _ : ZMod 2 => (lgF K0 l : MvPowerSeries Unit K0)) :=
    fun _ => FormalExponential.ip_lgF l σ hl hlK
  have h1 := hM K0 l 2 σ hU le_rfl (by decide) F hF be0 hF1 hF2 Unit _ _ (owOK_two σ)
    (trDual_two σ) ζ hζ Unit _ hST
  have hX : constantCoeff (PowerSeries.X : MvPowerSeries Unit K0) = 0 :=
    PowerSeries.constantCoeff_X
  have hlog : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K0) (lgF K0 l) = lgF K0 l :=
    PowerSeries.X_subst _
  have h2 : subst (fun _ : ZMod 2 => (lgF K0 l : MvPowerSeries Unit K0))
      (beTil (d := 2) l σ be0 (fun _ : Unit => (1 : K0)) (fun _ => 1)) =
      subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K0)) be0 := by
    rw [subst_tilde K0 l 2 σ hl be0 Unit _ _ Unit _ (fun _ => cc_lgF hl)]
    rw [Finset.univ_unique, Finset.sum_singleton, linEL_two, linOL_two]
    have h3 := addC_log exponential_specification hl hX hX be0
    rw [hlog] at h3
    rw [h3]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [h2] at h1
  have h4 := B4.simeq_sub_zero (htrans _ _ _ hph (hsymm _ _ h1))
  have h5 := Formalism.InvariantFactorPaths.G7.Top.lamModule K0 Unit l σ hp hU.2.2.1 hU.2.2.2.2 _ 2
    (by
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      have := hU.2.1
      omega) h4
  unfold Simeq at h5 ⊢
  have h2K : (2 : K0) ≠ 0 := two_ne_zero
  have e : ∀ B : MvPowerSeries Unit K0, (ph : MvPowerSeries Unit K0) - MvPowerSeries.C ((2 : K0)⁻¹) * B =
      MvPowerSeries.C (((2 : ℕ) : K0)⁻¹) * (MvPowerSeries.C (2 : K0) * ph - B) - 0 := by
    intro B
    rw [sub_zero, mul_sub, ← mul_assoc, ← map_mul]
    simp [h2K]
  rw [e]
  exact h5
end Formalism.L2.Th1.D
