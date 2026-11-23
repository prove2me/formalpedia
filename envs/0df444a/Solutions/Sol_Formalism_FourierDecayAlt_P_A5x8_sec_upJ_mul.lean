-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_upJ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:44.637863+00:00
-- url     : https://prove2.me/submissions/9b5651f8-63d3-4b26-89cb-e6e24e2bdb8f

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mul_up
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
theorem _root_.solution (h : Point K) (c : Kˣ) (u b : upUniG K h.1.sum) (η ρ : Fin h.1.sum → K) :
    sec_upJ h c u η * sec_upJ h c b ρ = sec_upJ h c (u * b) (ρ + (sec_m b)⁻¹ *ᵥ η) := by
  have hinv : sec_m b * (sec_m b)⁻¹ = 1 := by
    rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hub : sec_m (u * b) = sec_m u * sec_m b := rfl
  apply sec_m_ext
  rw [show sec_m (sec_upJ h c u η * sec_upJ h c b ρ) =
      sec_m (sec_upJ h c u η) * sec_m (sec_upJ h c b ρ) from rfl, sec_upJ_m, sec_upJ_m, sec_upJ_m,
    sec_mul_up, hub]
  congr 2
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.A5x8
