-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.subst_XX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:04.720832+00:00
-- url     : https://prove2.me/submissions/c156289f-d635-4267-9a25-ce728254d2e6

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef

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
theorem _root_.solution (G : MvPowerSeries (Fin 2) K) :
    G.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] = G := by
  have : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X := by
    funext i; fin_cases i <;> rfl
  rw [this, MvPowerSeries.subst_self]; rfl
end Formalism.ELL.FormalGroupPointsHom
