-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSeriesLimit.lead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:08.16944+00:00
-- url     : https://prove2.me/submissions/8e33b066-864f-4099-896d-c6129ddf6ac7

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
theorem _root_.solution {w : PowerSeries R} (hw : WFixed W w) :
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1 := by
  have hX : X ∣ w := X_dvd_iff.mpr hw.1
  have e0 : T W 0 = X ^ 3 := by simp only [T]; ring
  have hw2 : T W w = w := hw.2.symm
  have step : ∀ n, X ^ n ∣ w → X ^ (n + 1) ∣ w - X ^ 3 := by
    intro n h
    have e : w - X ^ 3 = (w - 0) * E W w 0 := by
      rw [← T_sub, e0, hw2]
    rw [e, sub_zero, pow_succ]
    exact mul_dvd_mul h (X_dvd_E W hX (dvd_zero X))
  have hadd : ∀ n, n ≤ 3 → X ^ n ∣ w - X ^ 3 → X ^ n ∣ w := by
    intro n hn h
    have := dvd_add h (pow_dvd_pow (X : PowerSeries R) hn)
    rwa [sub_add_cancel] at this
  have h1 : X ^ 1 ∣ w := by rw [pow_one]; exact hX
  have h2 : X ^ 2 ∣ w := hadd 2 (by norm_num) (step 1 h1)
  have h3 : X ^ 3 ∣ w := hadd 3 le_rfl (step 2 h2)
  have h4 : X ^ 4 ∣ w - X ^ 3 := step 3 h3
  have c := X_pow_dvd_iff.mp h3
  have c4 := X_pow_dvd_iff.mp h4 3 (by norm_num)
  rw [map_sub, coeff_X_pow_self] at c4
  exact ⟨c 0 (by norm_num), c 1 (by norm_num), c 2 (by norm_num), sub_eq_zero.mp c4⟩
end Formalism.ELL.WeierstrassSeriesLimit
