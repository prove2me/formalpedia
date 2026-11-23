-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LocalVolumePositivity.pos_MM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:25.372007+00:00
-- url     : https://prove2.me/submissions/4022307a-0ace-40a6-9263-82c0622c2c9c

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
theorem _root_.solution (hP : B.Pos) : 0 < B.MM := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.MM
  exact mul_pos xMo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.1)
end Formalism.FourierDecayAlt.P.LocalVolumePositivity
