-- Prove2me | solution 1 for Formalism.ELL.wFormalGroup_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:20.361117+00:00
-- url     : https://prove2.me/submissions/483f2547-c90b-482a-a9c4-ffe95a777f44

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_exists_unit_factor
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_assoc_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
namespace Formalism.ELL
theorem _root_.solution (hC : Formalism.ELL.WChordSeries.{u}) (hS : Formalism.ELL.WChordSubst.{u})
    (hP : Formalism.ELL.WPoint.{u}) : Formalism.ELL.WFormalGroup.{u} := by
  intro K _ W w hw
  obtain ⟨F₂, hcoef, h0, h1, h2, hch⟩ := hC K W w hw
  obtain ⟨u, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  let F : FormalGroup K :=
    { toPowerSeries := F₂
      zero_constantCoeff := h0
      lin_coeff_X := h1
      lin_coeff_Y := h2
      assoc := WeierstrassCoordinateSubstitution.assoc_of hS hP hw hwu hu F₂ h0 h1 hch }
  exact ⟨F, hcoef, hch⟩
end Formalism.ELL
