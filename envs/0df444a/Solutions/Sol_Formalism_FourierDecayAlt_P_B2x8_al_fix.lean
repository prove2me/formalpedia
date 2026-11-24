-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:01.401025+00:00
-- url     : https://prove2.me/submissions/38e09e22-41ac-4685-ad71-c778fe3b5ced

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_mem_UH_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_matrix_ext_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_levi_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_cL_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_cF_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution {h : Mat k (1 + r')} (hh : h ∈ GV k (1 + r')) (h1 : h *ᵥ e0 k r' = e0 k r')
    (h2 : h *ᵥ es0 k r' = es0 k r') : ∃ g₁ ∈ GV k r', h = ιLev k 1 r' g₁ := by
  have key : ∀ y, h *ᵥ mk3 k r' 0 y 0 = mk3 k r' 0 (LinearMap.toMatrix' (alL h) *ᵥ y) 0 := by
    intro y
    rw [LinearMap.toMatrix'_mulVec]
    have e1 : cL (h *ᵥ mk3 k r' 0 y 0) = 0 := by
      rw [← al_cL_eq]
      conv_lhs => rw [← h1]
      rw [herm_UH _ hh, al_cL_eq, three_block_last]
    have e2 : cF (h *ᵥ mk3 k r' 0 y 0) = 0 := by
      rw [← al_cF_eq]
      conv_lhs => rw [← h2]
      rw [herm_UH _ hh, al_cF_eq, three_block_first]
    conv_lhs => rw [← three_block_eta (h *ᵥ mk3 k r' 0 y 0), e1, e2]
    rfl
  refine ⟨LinearMap.toMatrix' (alL h), ?_, ?_⟩
  · apply mem_UH_of
    intro y y'
    have := herm_UH _ hh (mk3 k r' 0 y 0) (mk3 k r' 0 y' 0)
    rw [key, key, hermitian_three_block, hermitian_three_block] at this
    simpa using this
  · apply matrix_ext_three_block
    intro a y b
    rw [levi_three_block, three_block_split, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2, key,
      ← three_block_split]
end Formalism.FourierDecayAlt.P.B2x8
