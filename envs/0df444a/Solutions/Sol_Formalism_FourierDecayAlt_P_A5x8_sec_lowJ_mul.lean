-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_lowJ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:44.069641+00:00
-- url     : https://prove2.me/submissions/00e716f3-a492-4514-a0ac-378b6237c84b

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mul_low
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
theorem _root_.solution (h : Point K) (c : Kˣ) (a v : lowW K h.1 h.2) (ρ ξ : Fin h.1.sum → K) :
    sec_lowJ h c a ρ * sec_lowJ h c v ξ = sec_lowJ h c (a * v) (ρ + ξ ᵥ* (sec_m a)⁻¹) := by
  have hinv : (sec_m a)⁻¹ * sec_m a = 1 := by
    rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hav : sec_m (a * v) = sec_m a * sec_m v := rfl
  apply sec_m_ext
  rw [show sec_m (sec_lowJ h c a ρ * sec_lowJ h c v ξ) =
      sec_m (sec_lowJ h c a ρ) * sec_m (sec_lowJ h c v ξ) from rfl, sec_lowJ_m, sec_lowJ_m, sec_lowJ_m,
    sec_mul_low, hav]
  congr 2
  simp only [Matrix.add_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.A5x8
