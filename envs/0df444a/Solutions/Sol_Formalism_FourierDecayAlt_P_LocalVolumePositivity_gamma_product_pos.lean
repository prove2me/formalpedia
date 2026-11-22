-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LocalVolumePositivity.gamma_product_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:50.654109+00:00
-- url     : https://prove2.me/submissions/07dc4c2a-6dc2-4b54-b961-6cb666903441

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
theorem _root_.solution (hP : B.Pos) : 0 < B.Gam1 := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.Gam1
  exact prod_pos fun p _ => by unfold MassData.ga; exact div_pos (hp p).2.1 (hp p).2.2.1
end Formalism.FourierDecayAlt.P.LocalVolumePositivity
