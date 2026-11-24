-- Prove2me | solution 1 for Formalism.ELL.cube_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:48.743043+00:00
-- url     : https://prove2.me/submissions/d44d0bb4-9747-4591-a4b0-a0f2cd7ad032

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_chord_series_eq_F2
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_main
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_mem_T


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
theorem _root_.solution : Formalism.ELL.CubeTwo.{u} := by
  intro K _ W w F hw hF0 hch
  have hF := CubeTwoAlt.chord_series_eq_F2 hw hF0 hch
  subst hF
  obtain ⟨c, hcT, hcc, hc⟩ := CubeTwoAlt.main hw
  exact ⟨c, fun d => WeierstrassChordSeries.mem_T.mp hcT d, hcc, hc⟩
end Formalism.ELL
