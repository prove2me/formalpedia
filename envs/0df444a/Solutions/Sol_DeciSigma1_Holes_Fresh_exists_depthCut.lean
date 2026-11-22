-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.exists_depthCut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:26.798312+00:00
-- url     : https://prove2.me/submissions/11e5873f-36ae-42a3-9e15-e5419fc9db21

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) {q : ℕ} (hq : q ∈ anchors W t o.1)
    (hsq : o.2.1 < q) (hqe : q ≤ o.2.2) :
    ∃ d < lowerBlockCount W t o, depthCut W t o d = q := by
  let A := (anchors W t o.1).filter fun p => o.2.1 < p ∧ p ≤ o.2.2
  have hsub : (range (lowerBlockCount W t o)).image (depthCut W t o) ⊆ A := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
    have h := (depthCut_spec ho).1 d (mem_range.mp hd)
    exact mem_filter.mpr ⟨h.1, h.2.1, h.2.2.1⟩
  have hcard : ((range (lowerBlockCount W t o)).image (depthCut W t o)).card = A.card := by
    rw [card_image_iff.mpr, card_range]
    · rfl
    · intro a ha b hb heq
      have h1 := ((depthCut_spec ho).1 a (mem_range.mp ha)).2.2.2
      have h2 := ((depthCut_spec ho).1 b (mem_range.mp hb)).2.2.2
      rw [heq] at h1
      omega
  have heq := eq_of_subset_of_card_le hsub hcard.ge
  have hqA : q ∈ A := mem_filter.mpr ⟨hq, hsq, hqe⟩
  rw [← heq] at hqA
  obtain ⟨d, hd, heq⟩ := mem_image.mp hqA
  exact ⟨d, mem_range.mp hd, heq⟩
end DeciSigma1.Holes.Fresh
