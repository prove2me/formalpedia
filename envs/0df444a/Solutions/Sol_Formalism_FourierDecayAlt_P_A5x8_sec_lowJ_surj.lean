-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_lowJ_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:49:51.634848+00:00
-- url     : https://prove2.me/submissions/6bf09cc9-ba7f-4638-a699-24dff132dbae

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_m
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_inv_mul_one_low
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_addBlock_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (h : Point K) (c : Kˣ) (V : lowW K (addBlock h 1 c).1 (addBlock h 1 c).2) :
    ∃ v ξ, V = sec_lowJ h c v ξ := by
  obtain ⟨A, b, a, d, hM⟩ : ∃ A b a d, sec_m V = blkM (addBlock_sum h c) A b a d :=
    ⟨_, _, _, _, eq_blkM (addBlock_sum h c) (sec_m V)⟩
  have hV := V.2
  change IsLowUni (sec_m V) ∧ ∃ H, IsLowUni H ∧ sec_m V * _ = _ * H at hV
  obtain ⟨hA, hb, hd⟩ := (blkM_isLowUni _ _ _ _ _).1 (hM ▸ hV.1)
  subst hb hd
  rw [hM] at hV
  have hv := (sec_low_mem h c _ _).1 hV
  refine ⟨⟨sec_gl A (isLowUni_det K hA), hv⟩, a ᵥ* A⁻¹, ?_⟩
  apply sec_m_ext
  rw [sec_lowJ_m, hM]
  congr 1
  change _ = (a ᵥ* A⁻¹) ᵥ* A
  rw [Matrix.vecMul_vecMul, Formalism.DoubleCosetMeasures.P.Phase.inv_mul_one_low hA, Matrix.vecMul_one]
end Formalism.FourierDecayAlt.P.A5x8
