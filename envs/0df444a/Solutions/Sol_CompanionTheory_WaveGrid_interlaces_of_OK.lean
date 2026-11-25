-- Prove2me | solution 1 for CompanionTheory.WaveGrid.interlaces_of_OK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:37:42.754953+00:00
-- url     : https://prove2.me/submissions/d60a78b5-d34f-4a4d-95c6-244ec1105ba3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PstMul
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset
namespace CompanionTheory.WaveGrid
theorem _root_.solution (P : M.Par) (hOK : P.OK) : I.Interlaces P.k P.u P.u' P.lo := by
  intro i hi
  have hg := hOK.gap i hi
  unfold M.Par.lo M.Par.hi at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := min_le_left (P.u i) (P.u' i); linarith
  · have := min_le_right (P.u i) (P.u' i); linarith
  · have := le_max_left (P.u (i + 1)) (P.u' (i + 1)); linarith
  · have := le_max_right (P.u (i + 1)) (P.u' (i + 1)); linarith
end CompanionTheory.WaveGrid
