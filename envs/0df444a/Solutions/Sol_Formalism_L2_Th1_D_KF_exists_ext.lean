-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.exists_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:32.742802+00:00
-- url     : https://prove2.me/submissions/13fa70f9-2653-4922-964f-3dc881fa2c11

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_jBK_coe
import Theorems.Thm_Formalism_L2_Th1_D_KF_l_ne_zero_Kur
import Theorems.Thm_Formalism_L2_Th1_D_KF_jBK_away

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
theorem _root_.solution (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1)
    (g : ringB l →+* ℂ_[l]) (hg : ∀ x, g x ∈ ringB l) :
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, ∀ (x : MaximalUnramifiedExtension l) (hx : (x : ℂ_[l]) ∈ ringB l),
      (σ x : ℂ_[l]) = g ⟨x, hx⟩ := by
  letI := (jBK hB).toAlgebra
  haveI := jBK_away hB
  let ψ : ringB l →+* MaximalUnramifiedExtension l := (jBK hB).comp (g.codRestrict (ringB l) hg)
  have hu : IsUnit (ψ (l : ringB l)) := by
    rw [map_natCast]
    exact IsUnit.mk0 _ l_ne_zero_Kur
  refine ⟨IsLocalization.Away.lift (l : ringB l) hu, fun x hx => ?_⟩
  have key : IsLocalization.Away.lift (l : ringB l) hu (algebraMap (ringB l) (MaximalUnramifiedExtension l) ⟨x, hx⟩) =
      ψ ⟨x, hx⟩ := by
    first
      | exact IsLocalization.Away.lift_eq (S := MaximalUnramifiedExtension l) (l : ringB l) hu ⟨x, hx⟩
      | exact IsLocalization.lift_eq _ _
      | simp
  have hx' : algebraMap (ringB l) (MaximalUnramifiedExtension l) ⟨x, hx⟩ = x := Subtype.ext (jBK_coe hB _)
  rw [hx'] at key
  rw [key]
  rfl
end Formalism.L2.Th1.D.KF
