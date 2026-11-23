-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LocalVolumePositivity.pos_tt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:04.862307+00:00
-- url     : https://prove2.me/submissions/02d72945-8cc4-4803-bf06-e9e306710c02

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
theorem _root_.solution (hP : B.Pos) : 0 < B.tt := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.tt
  exact prod_pos fun p _ => add_pos one_pos (div_pos (by norm_num) (hp p).1)
end Formalism.FourierDecayAlt.P.LocalVolumePositivity
