-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSeriesLimit.lim_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:06.909635+00:00
-- url     : https://prove2.me/submissions/49c93e99-1107-4014-8968-d1cd0d2b6efc

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_contract
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_eq_zero_of_forall_X_pow_dvd
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_X_dvd_seq
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_lim_approx

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
theorem _root_.solution : WFixed W (lim W) := by
  have h1 := lim_approx W 1
  rw [pow_one] at h1
  have hX : X ∣ lim W := by
    have := dvd_add h1 (X_dvd_seq W 1)
    rwa [sub_add_cancel] at this
  refine ⟨X_dvd_iff.mp hX, ?_⟩
  show lim W = T W (lim W)
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_X_pow_dvd
  intro k
  have h2 := lim_approx W (k + 1)
  have h3 : X ^ (k + 1) ∣ T W (seq W k) - T W (lim W) :=
    contract W (X_dvd_seq W k) hX
      (by rw [← neg_sub]; exact dvd_neg.mpr (lim_approx W k))
  have e : lim W - T W (lim W)
      = (lim W - seq W (k + 1)) + (T W (seq W k) - T W (lim W)) := by
    rw [show seq W (k + 1) = T W (seq W k) from rfl]
    ring
  rw [e]
  exact (pow_dvd_pow X (Nat.le_succ k)).trans (dvd_add h2 h3)
end Formalism.ELL.WeierstrassSeriesLimit
