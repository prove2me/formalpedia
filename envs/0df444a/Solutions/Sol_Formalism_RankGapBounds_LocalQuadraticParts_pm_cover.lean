-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.pm_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:56.173478+00:00
-- url     : https://prove2.me/submissions/83641edd-a3e1-4ec9-bd74-14632cbc50e8

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.RankGapBounds.LocalQuadraticParts
open Finset
private theorem dvd_of_natCast_zmod_eq_zero {M a : ℕ} (h : (a : ZMod M) = 0) : M ∣ a := by
  exact (CharP.cast_eq_zero_iff (ZMod M) M a).mp h
end Formalism.RankGapBounds.LocalQuadraticParts
end

set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (M N : ℕ) (hM : 2 ≤ M) (s : Finset ℕ)
    (hs : ∀ l ∈ s, 3 ≤ l ∧ l ≤ N ∧ ((l : ZMod M) = 1 ∨ (l : ZMod M) = -1)) :
    s ⊆ (range N).image (fun k => (k + 1) * M + 1) ∪
      (range N).image (fun k => (k + 1) * M - 1) := by
  intro l hl
  obtain ⟨h3, hN, h⟩ := hs l hl
  simp only [mem_union, mem_image, mem_range]
  rcases h with h | h
  · left
    have hd : M ∣ l - 1 := dvd_of_natCast_zmod_eq_zero
      (by rw [Nat.cast_sub (by omega), Nat.cast_one, h, sub_self])
    obtain ⟨q, hq⟩ := hd
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, mul_zero] at hq; omega
      · exact h0
    have hqM : q ≤ M * q := by nlinarith
    refine ⟨q - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hq0, mul_comm]
    omega
  · right
    have hd : M ∣ l + 1 := dvd_of_natCast_zmod_eq_zero (by push_cast; rw [h]; ring)
    obtain ⟨q, hq⟩ := hd
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, mul_zero] at hq; omega
      · exact h0
    have h2q : 2 * q ≤ M * q := by nlinarith
    refine ⟨q - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hq0, mul_comm]
    omega
end Formalism.RankGapBounds.LocalQuadraticParts
