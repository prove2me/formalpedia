-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_phase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:44.201828+00:00
-- url     : https://prove2.me/submissions/e3fc8007-b5b6-4c2e-befa-220dcdf1a0f1

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_sLow
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_sUp
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lastE_vecMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lastE_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_upJ_m

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
variable {K : Type} [CommRing K]
variable {m N : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (h : Point K) (c : Kˣ) (p : lowW K h.1 h.2 × upUniG K h.1.sum)
    (ξ η : Fin h.1.sum → K) (ψ : AddChar K ℂ) :
    phase ψ ((sec_lowJ h c p.1 ξ, sec_upJ h c p.2 η) :
      lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 × upUniG K (addBlock h 1 c).1.sum) =
      phase ψ p * ψ (lastE ξ + lastE η) := by
  show ψ (sLow (sec_m (sec_lowJ h c p.1 ξ)) + sUp (sec_m (sec_upJ h c p.2 η))) =
    ψ (sLow (sec_m p.1) + sUp (sec_m p.2)) * ψ (lastE ξ + lastE η)
  rw [sec_lowJ_m, sec_upJ_m, sec_sLow, sec_sUp, sec_lastE_vecMul p.1.2.1, sec_lastE_mulVec p.2.2,
    ← AddChar.map_add_eq_mul]
  congr 1
  ring
end Formalism.FourierDecayAlt.P.A5x8
