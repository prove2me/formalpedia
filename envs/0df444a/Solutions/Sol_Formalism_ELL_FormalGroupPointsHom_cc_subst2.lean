-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.cc_subst2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:29.049957+00:00
-- url     : https://prove2.me/submissions/538026f3-b252-4ea0-b42f-d62b6387fc43

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [Field K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {G s t : MvPowerSeries (Fin 2) K} (hG : MvPowerSeries.constantCoeff G = 0)
    (hs : MvPowerSeries.constantCoeff s = 0) (ht : MvPowerSeries.constantCoeff t = 0) :
    MvPowerSeries.constantCoeff (G.subst ![s, t]) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst2 hs ht)
    (by intro i; fin_cases i <;> simp [hs, ht]) hG
end Formalism.ELL.FormalGroupPointsHom
