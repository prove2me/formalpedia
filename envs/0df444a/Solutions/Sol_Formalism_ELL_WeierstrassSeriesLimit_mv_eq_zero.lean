-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSeriesLimit.mv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:08.184937+00:00
-- url     : https://prove2.me/submissions/5ce6e83b-d1ff-480a-9514-6280ea961d59

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries

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
open Formalism.ELL.WeierstrassSeriesLimit
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.ELL.WeierstrassSeriesLimit
theorem _root_.solution {σ : Type*} {d e : MvPowerSeries σ R}
    (he : MvPowerSeries.constantCoeff e = 0) (h : d = d * e) : d = 0 := by
  have hc : IsUnit (MvPowerSeries.constantCoeff (1 - e)) := by
    rw [map_sub, map_one, he, sub_zero]
    exact isUnit_one
  have hu : IsUnit (1 - e) := MvPowerSeries.isUnit_iff_constantCoeff.mpr hc
  have h0 : d * (1 - e) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  exact hu.mul_left_eq_zero.mp h0
end Formalism.ELL.WeierstrassSeriesLimit
