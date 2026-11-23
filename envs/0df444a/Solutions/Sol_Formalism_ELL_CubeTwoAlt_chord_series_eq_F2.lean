-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.chord_series_eq_F2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:05.399093+00:00
-- url     : https://prove2.me/submissions/9da5e11c-3ae5-4313-b283-97c052f48951

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_w_eq_X_cube_mul_unit
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_wU_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_chord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_formalSum
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_eq_of_xy
import Theorems.Thm_Formalism_ELL_wSeriesSubstUnique_holds


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
open Formalism.ELL.CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {w : PowerSeries K}
namespace Formalism.ELL.CubeTwoAlt
theorem _root_.solution (hw : WFixed W w) {F : MvPowerSeries (Fin 2) K} (hF0 : cc F = 0)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F) : F = WeierstrassChordSeries.F2 W w := by
  have h2 := chord wSeriesSubstUnique_holds.{u} hw
  dsimp only [ChordAt] at hch h2
  exact WeierstrassCoordinateSubstitution.eq_of_xy (w_eq_X_cube_mul_unit hw) (wU_cc hw) F (WeierstrassChordSeries.F2 W w) hF0 (constantCoeff_formalSum hw)
    (hch.1.trans h2.1.symm) (hch.2.trans h2.2.symm)
end Formalism.ELL.CubeTwoAlt
