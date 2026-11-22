-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.ex_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:00:17.36626+00:00
-- url     : https://prove2.me/submissions/8cbe9191-893d-49cd-84c2-bb8318f96b8d

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
theorem _root_.solution {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) : ex N i j = N i j := by
  simp [ex]
end Formalism.FourierDecayAlt.P.StandardCharacterExists
