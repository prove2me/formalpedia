-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSeriesLimit.lim_approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:47.905325+00:00
-- url     : https://prove2.me/submissions/19a2e765-35b9-4b03-b770-73b5612dceb6

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_seq_far

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
theorem _root_.solution (k : ℕ) : X ^ k ∣ lim W - seq W k := by
  rw [X_pow_dvd_iff]
  intro m hm
  obtain ⟨i, rfl⟩ : ∃ i, k = m + 1 + i := ⟨k - (m + 1), by omega⟩
  have h := X_pow_dvd_iff.mp (seq_far W (m + 1) i) m (Nat.lt_succ_self m)
  simp only [map_sub, lim, coeff_mk] at h ⊢
  linear_combination -h
end Formalism.ELL.WeierstrassSeriesLimit
