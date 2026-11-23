-- Prove2me | solution 1 for Formalism.ELL.formal_group_points_hom_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:43.365956+00:00
-- url     : https://prove2.me/submissions/0462e996-9f63-4673-b745-aa2536e661dd

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_e1hom_main
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_eq_of_xy
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_exists_unit_factor


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
namespace Formalism.ELL
theorem _root_.solution (hU : Formalism.ELL.WSubstUnique.{u}) (hS : Formalism.ELL.WChordSubst.{u})
    (hFG : Formalism.ELL.WFormalGroup.{u}) (hPar : Formalism.ELL.FormalGroupPointsParametrisation.{u}) : Formalism.ELL.FormalGroupPointsHomomorphism.{u} := by
  intro K _ _ _ W w F₂ hW hw hF₂i hF₂0 hch P Q hP hQ
  obtain ⟨F, -, hFch⟩ := hFG K W w hw
  obtain ⟨u0, hwu, hu⟩ := Formalism.ELL.WeierstrassCoordinateSubstitution.exists_unit_factor hw
  have hFeq : F₂ = F.toPowerSeries :=
    Formalism.ELL.WeierstrassCoordinateSubstitution.eq_of_xy hwu hu _ _ hF₂0 F.zero_constantCoeff (hch.1.trans hFch.1.symm)
      (hch.2.trans hFch.2.symm)
  subst hFeq
  exact Formalism.ELL.FormalGroupPointsHom.e1hom_main hU hS hPar hW hw F hF₂i hch P Q hP hQ
end Formalism.ELL
