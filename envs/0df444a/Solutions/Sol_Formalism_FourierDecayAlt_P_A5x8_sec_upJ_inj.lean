-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_upJ_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:46.358943+00:00
-- url     : https://prove2.me/submissions/a8ef57dd-0356-4b7b-a50d-6a6bd44a9f7e

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_upJ_m
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
theorem _root_.solution (h : Point K) (c : Kˣ) {u u' : upUniG K h.1.sum} {η η' : Fin h.1.sum → K}
    (e : sec_upJ h c u η = sec_upJ h c u' η') : u = u' ∧ η = η' := by
  have e1 := congrArg sec_m e
  rw [sec_upJ_m, sec_upJ_m] at e1
  obtain ⟨hA, hb, -, -⟩ := blkM_inj _ e1
  have hu : u = u' := sec_m_ext hA
  subst hu
  refine ⟨rfl, ?_⟩
  have hinv : (sec_m u)⁻¹ * sec_m u = 1 := by
    rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (sec_m u)⁻¹ *ᵥ (sec_m u *ᵥ η) = (sec_m u)⁻¹ *ᵥ (sec_m u *ᵥ η') := by rw [hb]
  simpa [Matrix.mulVec_mulVec, hinv] using h2
end Formalism.FourierDecayAlt.P.A5x8
