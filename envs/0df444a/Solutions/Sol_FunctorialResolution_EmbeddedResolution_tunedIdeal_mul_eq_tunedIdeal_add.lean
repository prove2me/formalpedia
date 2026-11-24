-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tunedIdeal_mul_eq_tunedIdeal_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:42.060653+00:00
-- url     : https://prove2.me/submissions/14e15740-bc6d-4e77-9c7b-e6548f971e91

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdealPowers
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_sub
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_le_tuningWeight_eq_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_mul_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_le_tunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_mul_fun_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (J : Ideal S) (m L : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (r t : ℕ) (ht : (m - 1) * L ≤ t) :
    tunedIdeal k J m (r * L) * tunedIdeal k J m t = tunedIdeal k J m (r * L + t) := by
  refine le_antisymm (tunedIdeal_mul_le k J m _ _) ?_
  rw [tunedIdeal_le_iff]
  intro c hc
  have hc2 : r * L + (m - 1) * L ≤ tuningWeight m c :=
    le_trans (Nat.add_le_add_left ht (r * L)) hc
  obtain ⟨c', hc'le, hc'w⟩ := exists_le_tuningWeight_eq_mul m L r hL hdvd c hc2
  have h2 : (fun j => c' j + (c j - c' j)) = c := funext fun j => Nat.add_sub_cancel' (hc'le j)
  have hsplit : tuningMonomial k J m c' * tuningMonomial k J m (fun j => c j - c' j)
      = tuningMonomial k J m c := by
    rw [tuningMonomial_mul_fun_add k J m c' (fun j => c j - c' j), h2]
  rw [← hsplit]
  refine Ideal.mul_mono ?_ ?_
  · exact tuningMonomial_le_tunedIdeal k J m (r * L) c' (le_of_eq hc'w.symm)
  · refine tuningMonomial_le_tunedIdeal k J m t _ ?_
    rw [tuningWeight_sub m c c' hc'le, hc'w]
    have h9 : ∀ A B W : ℕ, A + B ≤ W → B ≤ W - A := by
      intro A B W h
      omega
    exact h9 (r * L) t (tuningWeight m c) hc
end FunctorialResolution.EmbeddedResolution
