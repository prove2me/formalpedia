-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.hjC_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:54.48689+00:00
-- url     : https://prove2.me/submissions/5745e693-1248-41df-9ddd-90b8c9551db0

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {σ : Type} (a : K) :
    algebraMap K (FractionRing (MvPowerSeries σ K)) a =
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (MvPowerSeries.C a) := by
  rw [IsScalarTower.algebraMap_apply K (MvPowerSeries σ K), MvPowerSeries.algebraMap_apply]
  rfl
end Formalism.ELL.FormalGroupPointsHom
