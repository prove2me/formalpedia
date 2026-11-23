-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSeriesLimit.fixed_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:56.328456+00:00
-- url     : https://prove2.me/submissions/5327fa17-dcf4-4578-ab14-776d16ef99d2

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_contract
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_eq_zero_of_forall_X_pow_dvd

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
theorem _root_.solution {w w' : PowerSeries R} (hw : WFixed W w) (hw' : WFixed W w') : w = w' := by
  have hX : X ∣ w := X_dvd_iff.mpr hw.1
  have hX' : X ∣ w' := X_dvd_iff.mpr hw'.1
  have key : ∀ k, X ^ k ∣ w - w' := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact one_dvd _
    | succ k ih =>
      have h := contract W hX hX' ih
      rwa [show T W w = w from hw.2.symm, show T W w' = w' from hw'.2.symm] at h
  exact sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd key)
end Formalism.ELL.WeierstrassSeriesLimit
