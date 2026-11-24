-- Prove2me | solution 1 for Formalism.L2.Th1.D.KurFrob_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:39:00.031343+00:00
-- url     : https://prove2.me/submissions/6ccee432-63a6-46a6-9857-26847d29c848

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_norm_l_eq
import Theorems.Thm_Formalism_L2_Th1_D_KF_frobenius_extension_on_inclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_frobenius_extension_mem
import Theorems.Thm_Formalism_L2_Th1_D_KF_frobenius_extension_congruence
import Theorems.Thm_Formalism_L2_Th1_D_KF_exists_ext

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
namespace Formalism.L2.Th1.D
theorem _root_.solution : FrobA → FrobAIsom → KurIntegers → KurUnram → KurFrob := by
  intro hF hI hK hU l hl hl2
  obtain ⟨σ0, hmu, hσ⟩ := hF l
  have hiso := hI l σ0 hσ
  obtain ⟨hB, -, -⟩ := hK l
  have hA : ∀ x ∈ ringA l, ‖x‖ ≤ 1 := fun x hx => ((hB x).1 (ringA_le_ringB l hx)).2
  obtain ⟨σ, hσe⟩ := exists_ext hB (sig1 σ0 hiso) (frobenius_extension_mem σ0 hiso)
  refine ⟨σ, ⟨hl.out, hl2, ?_, ?_, ?_⟩, ?_⟩
  · show ‖((l : MaximalUnramifiedExtension l) : ℂ_[l])‖ = _
    push_cast
    exact norm_l_eq l
  · intro a ha
    obtain ⟨k, hk⟩ := hU l (a : ℂ_[l]) a.2 (fun h => ha (Subtype.ext h))
    refine ⟨-k, ?_⟩
    show ‖(a : ℂ_[l])‖ = _
    rw [hk, norm_l_eq l, inv_zpow']
  · intro a ha
    have ha' : (a : ℂ_[l]) ∈ ringB l := (hB a).2 ⟨a.2, ha⟩
    have h1 := hσe a ha'
    show ‖((σ a - a ^ l : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ _
    push_cast
    rw [h1]
    exact frobenius_extension_congruence σ0 hiso hA hσ ⟨a, ha'⟩
  · intro ζ hζ
    have hζA : (ζ : ℂ_[l]) ∈ ringA l := Subring.subset_closure hζ
    have hζB := ringA_le_ringB l hζA
    apply Subtype.ext
    rw [hσe ζ hζB]
    have he : (⟨(ζ : ℂ_[l]), hζB⟩ : ringB l) = incAB l ⟨ζ, hζA⟩ := rfl
    rw [he, frobenius_extension_on_inclusion, hmu ⟨ζ, hζA⟩ hζ]
    simp
end Formalism.L2.Th1.D
