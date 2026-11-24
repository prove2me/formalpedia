-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.middle_level_volume_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:54.680155+00:00
-- url     : https://prove2.me/submissions/b4d33d40-85f4-4407-aa2b-a0161250fd80

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3
open LocalVolumePositivity
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : KnatGamma := by
  intro P _ B hP hI p
  obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hP.1 p
  obtain ⟨h1, h2⟩ := hI p
  rw [div_eq_iff qKp.ne'] at h2
  rw [h2, h1]
  unfold MassData.ga
  field_simp
end Formalism.FourierDecayAlt.P
