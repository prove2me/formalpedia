-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_lowJ_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:49:51.415423+00:00
-- url     : https://prove2.me/submissions/51e4cf6c-2610-48cf-b82c-8b653353049b

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_m
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
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (h : Point K) (c : Kˣ) {v v' : lowW K h.1 h.2} {ξ ξ' : Fin h.1.sum → K}
    (e : sec_lowJ h c v ξ = sec_lowJ h c v' ξ') : v = v' ∧ ξ = ξ' := by
  have e1 := congrArg sec_m e
  rw [sec_lowJ_m, sec_lowJ_m] at e1
  obtain ⟨hA, -, ha, -⟩ := blkM_inj _ e1
  have hv : v = v' := sec_m_ext hA
  subst hv
  refine ⟨rfl, ?_⟩
  have hinv : sec_m v * (sec_m v)⁻¹ = 1 := by
    rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ξ ᵥ* sec_m v ᵥ* (sec_m v)⁻¹ = ξ' ᵥ* sec_m v ᵥ* (sec_m v)⁻¹ := by rw [ha]
  simpa [Matrix.vecMul_vecMul, hinv] using h2
end Formalism.FourierDecayAlt.P.A5x8
