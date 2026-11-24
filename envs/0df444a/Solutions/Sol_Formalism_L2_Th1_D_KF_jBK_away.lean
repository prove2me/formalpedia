-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.jBK_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:23.338678+00:00
-- url     : https://prove2.me/submissions/c5a10bee-1f27-4881-9f41-6c051afc095d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_jBK_inj
import Theorems.Thm_Formalism_L2_Th1_D_KF_l_ne_zero_Kur
import Theorems.Thm_Formalism_L2_Th1_D_KF_jBK_surj

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
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open KF
open Formalism.L2.Th1.D.KF
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
variable (σ0 : ringA l →+* ringA l) (hiso : ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖)
namespace Formalism.L2.Th1.D.KF
theorem _root_.solution (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) :
    @IsLocalization.Away (ringB l) _ (l : ringB l) (MaximalUnramifiedExtension l) _ (jBK hB).toAlgebra := by
  letI := (jBK hB).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    show IsUnit (jBK hB ((l : ringB l) ^ n))
    rw [map_pow, map_natCast]
    exact (IsUnit.mk0 _ l_ne_zero_Kur).pow n
  · intro z
    obtain ⟨k, b, hb⟩ := jBK_surj hB z
    refine ⟨⟨b, ⟨(l : ringB l) ^ k, k, rfl⟩⟩, ?_⟩
    show z * jBK hB ((l : ringB l) ^ k) = jBK hB b
    rw [map_pow, map_natCast]
    exact hb
  · intro x y h
    exact ⟨1, by rw [jBK_inj hB h]⟩
end Formalism.L2.Th1.D.KF
