-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.map_mul_mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:39.559844+00:00
-- url     : https://prove2.me/submissions/d49fb19b-212d-4080-9b6e-72ec62b183cc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_map_mul_vol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P.StandardCharacterExists
theorem _root_.solution (β α : ℂ) (hα : α ≠ 0) :
    Measure.map (fun ρ : ℂ => α * ρ) (mu β) = Real.toNNReal ((‖α‖ ^ 2)⁻¹) • mu β := by
  unfold mu
  rw [Measure.map_smul, map_mul_vol α hα]
  rw [smul_comm]
  congr 1
end Formalism.FourierDecayAlt.P.StandardCharacterExists
