-- Prove2me | solution 1 for Formalism.GM.M.SSD.Good.mul_sfree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:34.211677+00:00
-- url     : https://prove2.me/submissions/08cb1c35-7b2f-41ed-b65a-9d0c9c8a11a7

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ ι K : Type} [CommRing K] [Nontrivial K] [DecidableEq σ] (sv : ι → σ)
namespace Formalism.GM.M.SSD
namespace Good
theorem _root_.solution {f Q : MvPolynomial σ K} {a : ι → ℕ} {s : σ →₀ ℕ} (hf : Good sv f a s)
    (hQ : SFree sv Q) :
    (∀ m ∈ (f * Q).support, sd sv m ≤ a) ∧ (∀ n, coeff (s + n) (f * Q) = coeff n Q) := by
  have hid : f * Q = monomial s 1 * Q + (f - monomial s 1) * Q := by ring
  have hR : ∀ m ∈ ((f - monomial s 1) * Q).support, sd sv m ≤ a ∧ sd sv m ≠ a := by
    intro m hm
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
    rw [sd_add, hQ w hw, add_zero]; exact hf.2 u hu
  refine ⟨?_, ?_⟩
  · intro m hm
    rw [hid] at hm
    rcases mem_support_add hm with hm | hm
    · obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
      rw [mem_support_monomial_one hu, sd_add, hQ w hw, add_zero, hf.1]
    · exact (hR m hm).1
  · intro n
    rw [hid, coeff_add, coeff_monomial_mul, one_mul]
    by_cases hn : n ∈ Q.support
    · have hz : coeff (s + n) ((f - monomial s 1) * Q) = 0 := by
        by_contra h
        have := hR _ (mem_support_iff.mpr h)
        rw [sd_add, hQ n hn, add_zero, hf.1] at this
        exact this.2 rfl
      rw [hz, add_zero]
    · rw [notMem_support_iff.mp hn]
      by_contra h
      rw [zero_add] at h
      obtain ⟨h1, h2⟩ := hR _ (mem_support_iff.mpr h)
      rw [sd_add, hf.1] at h1 h2
      apply h2
      exact le_antisymm h1 (fun k => Nat.le_add_right _ _)
end Good
end Formalism.GM.M.SSD
