-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.w_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:07.522676+00:00
-- url     : https://prove2.me/submissions/100a3764-1703-4826-a188-ff25b5a7671b

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_fw_cong

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
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
variable {W}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution {w : PowerSeries K} (hw : WFixed W w) :
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1 := by
  have hfix : fw W w = w := hw.2.symm
  have hXw : X ∣ w := PowerSeries.X_dvd_iff.mpr hw.1
  have h0 : fw W 0 = X ^ 3 := by simp [fw]
  have step : ∀ n, X ^ n ∣ w → X ^ (n + 1) ∣ w - X ^ 3 := fun n hn => by
    have := fw_cong W (n := n) (v := w) (v' := 0) (by simpa using hn) hXw (dvd_zero _)
    rwa [hfix, h0] at this
  have lift : ∀ n ≤ 3, X ^ n ∣ w - X ^ 3 → X ^ n ∣ w := fun n hn h => by
    have := dvd_add h (pow_dvd_pow (X : PowerSeries K) hn)
    simpa using this
  have h2 : X ^ 2 ∣ w := lift 2 (by norm_num) (step 1 (by simpa using hXw))
  have h3 : X ^ 3 ∣ w := lift 3 le_rfl (step 2 h2)
  have h4 := step 3 h3
  rw [PowerSeries.X_pow_dvd_iff] at h4
  have c : ∀ i < 4, coeff i w = if i = 3 then 1 else 0 := fun i hi => by
    have := h4 i hi
    rwa [map_sub, PowerSeries.coeff_X_pow, sub_eq_zero] at this
  exact ⟨by simpa using c 0 (by norm_num), by simpa using c 1 (by norm_num),
    by simpa using c 2 (by norm_num), by simpa using c 3 (by norm_num)⟩
end Formalism.ELL.WeierstrassChordSeries
