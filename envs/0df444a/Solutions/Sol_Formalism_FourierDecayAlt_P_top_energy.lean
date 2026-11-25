-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.top_energy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:55:40.988891+00:00
-- url     : https://prove2.me/submissions/ca310609-2b35-4349-985c-a367597e9f9e

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.TopE := by
  intro sd e h hs
  have h1 : (1 : ℝ) ≤ max sd 1 := le_max_right _ _
  have h2 : sd ≤ max sd 1 := le_max_left _ _
  have h3 : max sd 1 ≤ 2 := max_le hs (by norm_num)
  refine ⟨by linarith, by linarith, by linarith⟩
end Formalism.FourierDecayAlt.P
