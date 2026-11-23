-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.X_one_dvd_of_subst_X_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:38.462205+00:00
-- url     : https://prove2.me/submissions/0da5bfe1-e259-472a-a9de-4c5b3fb93d46

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_coeff_subst_X0_zero

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
namespace Formalism.ELL.CubeTwoAlt
theorem _root_.solution (H : MvPowerSeries (Fin 2) K)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] = 0) :
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ H := by
  rw [MvPowerSeries.X_dvd_iff]
  intro m hm
  rw [← coeff_subst_X0_zero H m hm, h, map_zero]
end Formalism.ELL.CubeTwoAlt
