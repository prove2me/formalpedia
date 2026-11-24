-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.jBK_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:09:25.939633+00:00
-- url     : https://prove2.me/submissions/221a41eb-e08d-43ea-9852-b362789472e8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_norm_l_eq
import Theorems.Thm_Formalism_L2_Th1_D_KF_l_pos_real
import Theorems.Thm_Formalism_L2_Th1_D_KF_jBK_coe

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
theorem _root_.solution (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) (z : MaximalUnramifiedExtension l) :
    ∃ (k : ℕ) (b : ringB l), z * (l : MaximalUnramifiedExtension l) ^ k = jBK hB b := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖(z : ℂ_[l])‖ (by exact_mod_cast hl.out.one_lt : (1 : ℝ) < l)
  have hmem : ((z * (l : MaximalUnramifiedExtension l) ^ k : MaximalUnramifiedExtension l) : ℂ_[l]) ∈ ringB l := by
    rw [hB]
    refine ⟨(z * (l : MaximalUnramifiedExtension l) ^ k).2, ?_⟩
    push_cast
    rw [norm_mul, norm_pow, norm_l_eq l, inv_pow, ← div_eq_mul_inv]
    exact (div_le_one (pow_pos (l_pos_real l) k)).mpr hk.le
  exact ⟨k, ⟨_, hmem⟩, Subtype.ext (jBK_coe hB ⟨_, hmem⟩).symm⟩
end Formalism.L2.Th1.D.KF
