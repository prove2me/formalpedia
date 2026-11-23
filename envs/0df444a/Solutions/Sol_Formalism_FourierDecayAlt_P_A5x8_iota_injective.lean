-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iota_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:57.830177+00:00
-- url     : https://prove2.me/submissions/496ad04d-beab-4d50-aee9-101ff3572c28

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iA_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iC_injective
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (R : Subring K) {m m' : ℕ} (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (h₁ : IsInt R Z₁) (h₂ : IsInt R Z₂) (d₁ : IsUnit Z₁.det)
    (d₂ : IsUnit Z₂.det) : Function.Injective (iota R Z₁ Z₂) := by
  rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ ⟨⟨x, y⟩, ⟨x', y'⟩⟩ h
  simp only [iota, Prod.mk.injEq] at h
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := h
  rw [iA_injective R Z₁ e1, iC_injective R Z₁ h₁ d₁ e2, iA_injective R Z₂ e3,
    iC_injective R Z₂ h₂ d₂ e4]
end Formalism.FourierDecayAlt.P.A5x8
