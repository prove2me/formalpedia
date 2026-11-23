-- Prove2me | solution 1 for Formalism.ELL.WeierstrassCoordinateSubstitution.isUnit_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:01.607413+00:00
-- url     : https://prove2.me/submissions/0a233a97-e8be-4365-a273-a81352469f8f

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
theorem _root_.solution {u : PowerSeries K} (hu : constantCoeff u = 1) {σ : Type}
    (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) :
    IsUnit (u.subst s) := by
  have ha : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  obtain ⟨u', hu'⟩ := PowerSeries.X_dvd_iff.mpr (show constantCoeff (u - 1) = 0 by simp [hu])
  have h1 : u = 1 + X * u' := by rw [← hu']; ring
  rw [MvPowerSeries.isUnit_iff_constantCoeff, h1, ← PowerSeries.coe_substAlgHom ha, map_add,
    map_one, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]
  simp [hs]
end Formalism.ELL.WeierstrassCoordinateSubstitution
