-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.rel_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:09.929659+00:00
-- url     : https://prove2.me/submissions/d12ec5fa-0ab1-44ec-9b9c-67683b50f0e0

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution {S : Type*} [CommRing S] (e h : ℕ → S) (k : ℕ)
    (H : ∑ i ∈ range (k + 1), (-1) ^ i * e i * h (k - i) = 0) :
    ∑ i ∈ range (k + 1), (-1) ^ i * h i * e (k - i) = 0 := by
  have h1 := Finset.sum_range_reflect (fun i => (-1 : S) ^ i * e i * h (k - i)) (k + 1)
  rw [H] at h1
  have h2 : ∑ i ∈ range (k + 1), (-1) ^ i * h i * e (k - i) =
      (-1) ^ k * ∑ j ∈ range (k + 1), (fun i => (-1 : S) ^ i * e i * h (k - i)) (k + 1 - 1 - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [show k + 1 - 1 - j = k - j by omega, show k - (k - j) = j by omega]
    have hk : (-1 : S) ^ k = (-1) ^ (k - j) * (-1) ^ j := by
      rw [← pow_add, show k - j + j = k by omega]
    have hsq : ((-1 : S) ^ (k - j)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [hk]
    linear_combination (-((-1 : S) ^ j * h j * e (k - j))) * hsq
  rw [h2, h1, mul_zero]
end Formalism.FT.SymmetricSeries
