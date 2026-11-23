-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.wMat_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:22.210793+00:00
-- url     : https://prove2.me/submissions/c84a684c-c8db-4b5c-912f-8c9c11c93f65

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
theorem _root_.solution {d : ℕ} (b : Fin d → ℂ) (i : Fin d) : (wMat d *ᵥ b) i = b i.rev := by
  simp [Matrix.mulVec, dotProduct, wMat]
end Formalism.FourierDecayAlt.P.StandardCharacterExists
