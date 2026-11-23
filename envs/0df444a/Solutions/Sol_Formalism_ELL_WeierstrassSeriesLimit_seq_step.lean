-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSeriesLimit.seq_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:29.290416+00:00
-- url     : https://prove2.me/submissions/6bc435c6-620b-41c9-afd7-e99db09fa63c

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_contract
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_X_dvd_seq

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
theorem _root_.solution (k : ℕ) : X ^ k ∣ seq W (k + 1) - seq W k := by
  induction k with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    show X ^ (k + 1) ∣ T W (seq W (k + 1)) - T W (seq W k)
    exact contract W (X_dvd_seq W _) (X_dvd_seq W _) ih
end Formalism.ELL.WeierstrassSeriesLimit
