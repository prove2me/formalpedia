-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iC_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:52.632646+00:00
-- url     : https://prove2.me/submissions/a9e21b4c-2a41-4e39-a497-068d8f1d4d6b

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_mk_outV
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_liftR_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
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
variable {K : Type} [CommRing K] (R : Subring K) {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (Z : Matrix (Fin m) (Fin m) K) (hZ : IsInt R Z) (hd : IsUnit Z.det)
    (β : coker R Z) : ∃ b : Fin m → R, coeLin R b = Z *ᵥ outV R (iC R Z β) ∧
      Submodule.Quotient.mk b = β := by
  have h1 : ∀ j, outV R (iC R Z β) j - (Z⁻¹ *ᵥ coeLin R (Quotient.out β)) j ∈ R := by
    intro j
    rw [← A5x3.mk_eq_mk, mk_outV]
    rfl
  let r : Fin m → R := fun j => ⟨_, h1 j⟩
  have hr : outV R (iC R Z β) = Z⁻¹ *ᵥ coeLin R (Quotient.out β) + coeLin R r := by
    funext j
    rw [Pi.add_apply, P.coeLin_apply]
    simp [r]
  have h2 : Z *ᵥ outV R (iC R Z β) = coeLin R (Quotient.out β) + Z *ᵥ coeLin R r := by
    rw [hr, mulVec_add, mulVec_mulVec, Matrix.mul_nonsing_inv Z hd, one_mulVec]
  have h3 : Z *ᵥ coeLin R r = coeLin R (P.liftR R Z hZ *ᵥ r) := by
    rw [P.coeLin_mulVec, P.liftR_map]
  refine ⟨Quotient.out β + P.liftR R Z hZ *ᵥ r, ?_, ?_⟩
  · rw [map_add, h2, h3]
  · rw [Submodule.Quotient.mk_add]
    have h4 : (Submodule.Quotient.mk (P.liftR R Z hZ *ᵥ r) : coker R Z) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, P.mem_latZ]
      exact ⟨r, h3⟩
    rw [h4, add_zero]
    exact Quotient.out_eq β
end Formalism.FourierDecayAlt.P.A5x8
