-- Prove2me | solution 1 for Formalism.ELL.WeierstrassCoordinateSubstitution.subst_w
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:30.928737+00:00
-- url     : https://prove2.me/submissions/4bec8ee4-ca6f-4073-91df-225642a48ba6

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor

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
open Formalism.ELL.WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]
namespace Formalism.ELL.WeierstrassCoordinateSubstitution
theorem _root_.solution {u w : PowerSeries K} (hwu : w = X ^ 3 * u) {σ : Type}
    (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) :
    w.subst s = s ^ 3 * u.subst s := by
  have ha : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  rw [hwu, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]
end Formalism.ELL.WeierstrassCoordinateSubstitution
