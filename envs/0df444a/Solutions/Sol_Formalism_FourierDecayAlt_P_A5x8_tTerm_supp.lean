-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.tTerm_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:57.142885+00:00
-- url     : https://prove2.me/submissions/e430d686-7e9c-4664-9240-df5a506e8d37

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_mem_range_iA
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_mem_range_iC
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_tTerm_mk
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
theorem _root_.solution (R : Subring K) (ψ : AddChar K ℂ) {m m' N N' : ℕ} (hN : N = m + 1)
    (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K) (Z₂ : Matrix (Fin m') (Fin m') K) (c : K)
    (d₁ : IsUnit Z₁.det) (d₂ : IsUnit Z₂.det) :
    Function.support (tTerm R ψ hN hN' Z₁ Z₂ c) ⊆ Set.range (iota R Z₁ Z₂) := by
  rintro ⟨⟨x, y⟩, ⟨x', y'⟩⟩ hy
  by_cases hI : IsInt R (bigZ hN Z₁ (outV R x) (outV R y) c) ∧
      IsInt R (bigZ hN' Z₂ (outV R x') (outV R y') c)
  · obtain ⟨hI1, hI2⟩ := hI
    unfold bigZ at hI1 hI2
    rw [blkM_isInt] at hI1 hI2
    obtain ⟨a, rfl⟩ := mem_range_iA R Z₁ x hI1.2.2.1
    obtain ⟨b, rfl⟩ := mem_range_iC R Z₁ d₁ y hI1.2.1
    obtain ⟨a', rfl⟩ := mem_range_iA R Z₂ x' hI2.2.2.1
    obtain ⟨b', rfl⟩ := mem_range_iC R Z₂ d₂ y' hI2.2.1
    exact ⟨((a, b), (a', b')), rfl⟩
  · exfalso
    apply hy
    rw [tTerm_mk, if_neg hI]
    simp
end Formalism.FourierDecayAlt.P.A5x8
