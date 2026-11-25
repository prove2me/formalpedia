-- Prove2me | solution 1 for Formalism.L2.Th1.D.IPLemma_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:57.689798+00:00
-- url     : https://prove2.me/submissions/187a596a-7d69-454d-a288-e84e92db5b8b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Lemmata_GeneralBFactUpper_Imports
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Theorems.Thm_Formalism_L2_Th1_D_ip_map_lgF
import Theorems.Thm_Formalism_L2_Th1_D_ip_lgF_funEq
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_funEqHomV
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow
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
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK frobVar frobVar_eq_expand)
namespace Formalism.L2.Th1.D
theorem _root_.solution : FrobSq → IPLemma := by
  intro hF K _ _ _ l σ h τ _ g hg
  obtain ⟨hset, _⟩ := hF K l σ h
  have hl : l.Prime := h.1
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.ne_zero
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hid : Formalism.FG.IsIdMod2 (fun _ : Unit => (lgF K l : MvPowerSeries Unit K)) := by
    refine ⟨fun _ => ?_, fun j i => ?_⟩
    · by_contra hc
      have hc' : PowerSeries.coeff 0 (lgF K l) ≠ 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff]
        exact hc
      obtain ⟨j, hj⟩ := Formalism.InvariantFactorPaths.G7.coeff_lgF_ne_zero hc'
      exact (pow_ne_zero j hq) hj.symm
    · have h1 := Formalism.InvariantFactorPaths.G7.coeff_lgF_pow K hl.two_le 0
      simp only [pow_zero, inv_one] at h1
      rw [if_pos (Subsingleton.elim i j)]
      exact h1
  have hf : Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (fun _ _ : Unit => (1 : K))
      (fun _ : Unit => (lgF K l : MvPowerSeries Unit K)) := by
    intro _
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    rw [ip_map_lgF, ip_lgF_funEq hl.two_le hlK hq]
    intro d
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp
  have hgt : Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (fun _ _ : Unit => (1 : K))
      (fun _ : Unit => g) := by
    intro _
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    rw [MvPowerSeries.smul_eq_C_mul, ← frobVar_eq_expand hq]
    exact hg.2
  obtain ⟨hh, h0, hI, hs⟩ := Formalism.FG.funEqHomV K l (l ^ 2) hq (σ.comp σ) hset Unit
    (fun _ _ => 1) (fun _ _ => by simp) (fun _ => lgF K l) hid hf τ (fun _ => g)
    (fun _ => hg.1) hgt
  exact ⟨hh (), h0 (), hI (), hs ()⟩
end Formalism.L2.Th1.D
