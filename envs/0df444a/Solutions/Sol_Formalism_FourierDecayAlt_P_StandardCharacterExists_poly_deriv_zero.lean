-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.poly_deriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:03.536568+00:00
-- url     : https://prove2.me/submissions/69db37ad-8bad-4bf1-9028-072aa0937642

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
theorem _root_.solution (c : ℕ → ℂ) :
    HasDerivAt (fun t : ℂ => ∑ j ∈ Finset.range (0 + 1), c j * t ^ (0 - j)) 0 0 := by
  simpa using hasDerivAt_const (0 : ℂ) (c 0)
end Formalism.FourierDecayAlt.P.StandardCharacterExists
