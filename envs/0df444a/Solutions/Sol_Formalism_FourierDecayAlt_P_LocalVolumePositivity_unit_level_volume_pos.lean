-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LocalVolumePositivity.unit_level_volume_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:54:37.324351+00:00
-- url     : https://prove2.me/submissions/bb3fd2ba-c521-4d65-ab53-0e11b0dc7510

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
open Formalism.FourierDecayAlt.P.LocalVolumePositivity
variable {P : Type} [Fintype P] {B : MassData P}
namespace Formalism.FourierDecayAlt.P.LocalVolumePositivity
theorem _root_.solution (hP : B.Pos) : 0 < B.unitLevelVolume := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.unitLevelVolume
  exact mul_pos xU0 (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2)
end Formalism.FourierDecayAlt.P.LocalVolumePositivity
