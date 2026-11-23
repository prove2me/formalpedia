-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jacobian_natural_measure_constant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:32.659817+00:00
-- url     : https://prove2.me/submissions/9729a4bb-4121-4bbd-b8dc-1b51f0e84339

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_unit_level_volume_pos

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
theorem _root_.solution : JacobianConstant := by
  intro P _ B hP hJ hNu
  have hU := unit_level_volume_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  rw [hJ, hNu]
  field_simp
end Formalism.FourierDecayAlt.P
