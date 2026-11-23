-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.strictUpper_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:22.596874+00:00
-- url     : https://prove2.me/submissions/2c9da324-0f0b-4c6c-8b3c-783a9107f3f9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists

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
theorem _root_.solution {d : ℕ} (a : ℂ) (y : UT d → ℂ) : strictUpper (a • y) = a • strictUpper y := by
  ext i j
  by_cases h : i < j <;> simp [strictUpper, h]
end Formalism.FourierDecayAlt.P.StandardCharacterExists
