-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSeriesLimit.contract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:38.082165+00:00
-- url     : https://prove2.me/submissions/b97b65ac-efff-4f02-85f2-95185d7494ba

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_T_sub
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_X_dvd_E

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
theorem _root_.solution {k : ℕ} {a b : PowerSeries R} (ha : X ∣ a) (hb : X ∣ b) (h : X ^ k ∣ a - b) :
    X ^ (k + 1) ∣ T W a - T W b := by
  rw [T_sub, pow_succ]
  exact mul_dvd_mul h (X_dvd_E W ha hb)
end Formalism.ELL.WeierstrassSeriesLimit
