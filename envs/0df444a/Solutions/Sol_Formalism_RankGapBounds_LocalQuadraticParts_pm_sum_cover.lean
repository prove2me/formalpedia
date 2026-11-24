-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.pm_sum_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:44:07.6755+00:00
-- url     : https://prove2.me/submissions/29e6fca7-42cf-4772-b5c4-2b3706306a51

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (f : ℕ → ℝ) (hf : ∀ l, 0 ≤ f l) (M N : ℕ) (hM : 2 ≤ M) (s : Finset ℕ)
    (hs : ∀ l ∈ s, 3 ≤ l ∧ l ≤ N ∧ ((l : ZMod M) = 1 ∨ (l : ZMod M) = -1)) :
    ∑ l ∈ s, f l ≤
      ∑ k ∈ range N, f ((k + 1) * M + 1) + ∑ k ∈ range N, f ((k + 1) * M - 1) := by
  have hMpos : 0 < M := by omega
  have hsub := pm_cover M N hM s hs
  have hinj1 : Set.InjOn (fun k : ℕ => (k + 1) * M + 1) ((range N : Finset ℕ) : Set ℕ) := by
    intro a _ b _ hab
    have hab' : (a + 1) * M + 1 = (b + 1) * M + 1 := hab
    have h' : (a + 1) * M = (b + 1) * M := by omega
    have := Nat.eq_of_mul_eq_mul_right hMpos h'
    omega
  have hinj2 : Set.InjOn (fun k : ℕ => (k + 1) * M - 1) ((range N : Finset ℕ) : Set ℕ) := by
    intro a _ b _ hab
    have hab' : (a + 1) * M - 1 = (b + 1) * M - 1 := hab
    have ha : 0 < (a + 1) * M := Nat.mul_pos (Nat.succ_pos a) hMpos
    have hb : 0 < (b + 1) * M := Nat.mul_pos (Nat.succ_pos b) hMpos
    have h' : (a + 1) * M = (b + 1) * M := by omega
    have := Nat.eq_of_mul_eq_mul_right hMpos h'
    omega
  set A := (range N).image (fun k => (k + 1) * M + 1) with hA
  set B := (range N).image (fun k => (k + 1) * M - 1) with hB
  have hU : ∑ x ∈ A ∪ B, f x + ∑ x ∈ A ∩ B, f x = ∑ x ∈ A, f x + ∑ x ∈ B, f x :=
    Finset.sum_union_inter
  have hI0 : 0 ≤ ∑ x ∈ A ∩ B, f x := sum_nonneg (fun i _ => hf i)
  have hsA : ∑ x ∈ A, f x = ∑ k ∈ range N, f ((k + 1) * M + 1) := sum_image hinj1
  have hsB : ∑ x ∈ B, f x = ∑ k ∈ range N, f ((k + 1) * M - 1) := sum_image hinj2
  have hs1 : ∑ l ∈ s, f l ≤ ∑ x ∈ A ∪ B, f x :=
    sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf i)
  linarith
end Formalism.RankGapBounds.LocalQuadraticParts
