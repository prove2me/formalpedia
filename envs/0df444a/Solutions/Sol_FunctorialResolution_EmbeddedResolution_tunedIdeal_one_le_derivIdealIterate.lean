-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tunedIdeal_one_le_derivIdealIterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:27:45.406383+00:00
-- url     : https://prove2.me/submissions/1f8257cf-2b55-4402-837d-34a6a918e86a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_eq_sum
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_eq_prod
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_le_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
section
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
private theorem exists_ne_zero_of_one_le_tuningWeight {m : ℕ} {c : ℕ → ℕ}
    (hc : 1 ≤ tuningWeight m c) : ∃ j ∈ Finset.range m, c j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz : tuningWeight m c = 0 := by
    rw [tuningWeight_eq_sum]
    exact Finset.sum_eq_zero fun j hj => by rw [hcon j hj, Nat.mul_zero]
  rw [hz] at hc
  exact Nat.not_succ_le_zero 0 hc
section
variable [Algebra ℚ S]
end
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (J : Ideal S) (m : ℕ) (_hm : 1 ≤ m) :
    tunedIdeal k J m 1 ≤ derivIdealIterate k (m - 1) J := by
  rw [tunedIdeal_le_iff]
  intro c hc
  obtain ⟨j, hj, hcj⟩ := exists_ne_zero_of_one_le_tuningWeight hc
  have hjm : j ≤ m - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
  refine le_trans ?_ (derivIdealIterate_le_of_le k hjm J)
  have hsplit : derivIdealIterate k j J ^ c j *
      ∏ x ∈ (Finset.range m).erase j, derivIdealIterate k x J ^ c x =
      ∏ x ∈ Finset.range m, derivIdealIterate k x J ^ c x :=
    Finset.mul_prod_erase (Finset.range m) (fun x => derivIdealIterate k x J ^ c x) hj
  rw [tuningMonomial_eq_prod, ← hsplit]
  exact le_trans Ideal.mul_le_left (Ideal.pow_le_self hcj)
end FunctorialResolution.EmbeddedResolution
