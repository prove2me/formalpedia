-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_upJ_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:46.488286+00:00
-- url     : https://prove2.me/submissions/1b7b924d-135d-4d27-8f03-dd0eac19a2df

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_upJ_m
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
theorem _root_.solution (h : Point K) (c : Kˣ) (V : upUniG K (addBlock h 1 c).1.sum) :
    ∃ u η, V = sec_upJ h c u η := by
  have hE := eq_blkM (addBlock_sum h c) (sec_m V)
  set A := Matrix.of fun i j => sec_m V (eN (addBlock_sum h c) (Sum.inl i)) (eN (addBlock_sum h c) (Sum.inl j))
    with hA
  set b := fun i => sec_m V (eN (addBlock_sum h c) (Sum.inl i)) (eN (addBlock_sum h c) (Sum.inr ())) with hb
  set a := fun j => sec_m V (eN (addBlock_sum h c) (Sum.inr ())) (eN (addBlock_sum h c) (Sum.inl j)) with ha
  set d := sec_m V (eN (addBlock_sum h c) (Sum.inr ())) (eN (addBlock_sum h c) (Sum.inr ())) with hd
  have hU : IsUpUni (blkM (addBlock_sum h c) A b a d) := by
    rw [← hE]
    exact V.2
  obtain ⟨hAu, ha0, hd1⟩ := (blkM_isUpUni _ _ _ _ _).1 hU
  have hdet : A.det = 1 := isUpUni_det K hAu
  refine ⟨⟨sec_gl A hdet, hAu⟩, A⁻¹ *ᵥ b, ?_⟩
  apply sec_m_ext
  rw [sec_upJ_m]
  show sec_m V = blkM (addBlock_sum h c) A (A *ᵥ (A⁻¹ *ᵥ b)) 0 1
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (by rw [hdet]; exact isUnit_one), Matrix.one_mulVec,
    ← ha0, ← hd1]
  exact hE
end Formalism.FourierDecayAlt.P.A5x8
