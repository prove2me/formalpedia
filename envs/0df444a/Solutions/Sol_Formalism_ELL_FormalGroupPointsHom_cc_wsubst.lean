-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.cc_wsubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:48.532954+00:00
-- url     : https://prove2.me/submissions/3e25b512-b90f-4e34-97ca-ba76c0f96279

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_exists_unit_factor
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_subst_w


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
theorem _root_.solution {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w) {σ : Type}
    {s : MvPowerSeries σ K} (hs : MvPowerSeries.constantCoeff s = 0) :
    MvPowerSeries.constantCoeff (w.subst s) = 0 := by
  obtain ⟨u0, hwu, _⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  rw [WeierstrassCoordinateSubstitution.subst_w hwu s hs, map_mul, map_pow, hs]; simp
end Formalism.ELL.FormalGroupPointsHom
