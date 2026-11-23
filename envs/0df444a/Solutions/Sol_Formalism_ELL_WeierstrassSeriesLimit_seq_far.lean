-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSeriesLimit.seq_far
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:09.563661+00:00
-- url     : https://prove2.me/submissions/22994097-48d7-4b92-af10-dca691047918

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_seq_step

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
theorem _root_.solution (j i : ℕ) : X ^ j ∣ seq W (j + i) - seq W j := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := seq_step W (j + i)
    have h2 : (X : PowerSeries R) ^ j ∣ X ^ (j + i) := pow_dvd_pow X (Nat.le_add_right j i)
    have e : j + (i + 1) = j + i + 1 := by omega
    rw [e, show seq W (j + i + 1) - seq W j
      = (seq W (j + i + 1) - seq W (j + i)) + (seq W (j + i) - seq W j) by ring]
    exact dvd_add (h2.trans h1) ih
end Formalism.ELL.WeierstrassSeriesLimit
