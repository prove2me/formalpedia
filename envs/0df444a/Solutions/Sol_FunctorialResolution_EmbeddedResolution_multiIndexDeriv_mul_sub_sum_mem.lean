-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.multiIndexDeriv_mul_sub_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:03:57.103194+00:00
-- url     : https://prove2.me/submissions/afc0a78a-0b5d-45fe-9fae-74b7b7d2a7ff

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_mem_pow_sub
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {h : ℕ} (D : Fin h → Derivation k R R) (J : Ideal R)
    (r s : ℕ) (α : Fin h → ℕ) (hα : ∑ i, α i = r + s) {f g : R}
    (hf : f ∈ J ^ r) (hg : g ∈ J ^ s) :
    multiIndexDeriv D α (f * g) -
        ∑ β ∈ (Fintype.piFinset fun i => Finset.range (α i + 1)).filter
            (fun β => ∑ i, β i = r),
          ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
            multiIndexDeriv D (fun i => α i - β i) g ∈ J := by
  rw [multiIndexDeriv_mul D α f g,
    ← Finset.sum_filter_add_sum_filter_not
      (Fintype.piFinset fun i => Finset.range (α i + 1)) (fun β => ∑ i, β i = r),
    add_sub_cancel_left]
  refine Ideal.sum_mem _ ?_
  intro β hβ
  rw [Finset.mem_filter] at hβ
  obtain ⟨hβmem, hβne⟩ := hβ
  have hβi : ∀ i, β i ≤ α i := fun i =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hβmem i))
  have h1 : (∑ i, (α i - β i)) + ∑ i, β i = r + s := by
    rw [← hα, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hβi i)
  by_cases hlt : ∑ i, β i < r
  · have hmem : multiIndexDeriv D β f ∈ J ^ (r - ∑ i, β i) :=
      multiIndexDeriv_mem_pow_sub D J r hf β
    have hx : multiIndexDeriv D β f ∈ J := by
      have hpos : 0 < r - ∑ i, β i := by omega
      exact Ideal.pow_le_self hpos.ne' hmem
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hx)
  · have hmem : multiIndexDeriv D (fun i => α i - β i) g ∈ J ^ (s - ∑ i, (α i - β i)) :=
      multiIndexDeriv_mem_pow_sub D J s hg (fun i => α i - β i)
    have hy : multiIndexDeriv D (fun i => α i - β i) g ∈ J := by
      have hpos : 0 < s - ∑ i, (α i - β i) := by omega
      exact Ideal.pow_le_self hpos.ne' hmem
    exact Ideal.mul_mem_left _ _ hy
end FunctorialResolution.EmbeddedResolution
