-- Prove2me | solution 1 for Galvin.exists_listColoring_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:37:48.245338+00:00
-- url     : https://prove2.me/submissions/ee86feb4-be47-470e-a1b4-d68b6f3d331e

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Definitions.Def_GalvinLib_Kernel

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset
namespace Galvin
theorem _root_.solution {α Color : Type*} [Nonempty Color]
    (G : SimpleGraph α) (D : α → α → Prop) [DecidableRel D] (hK : HasKernels G D) :
    ∀ (n : ℕ) (U : Finset α), U.card = n → ∀ L : α → Finset Color,
      (∀ x ∈ U, (U.filter (D x ·)).card < (L x).card) →
      ∃ c : α → Color, (∀ x ∈ U, c x ∈ L x) ∧
        ∀ x ∈ U, ∀ y ∈ U, G.Adj x y → c x ≠ c y := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn L hL
  rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨fun _ => Classical.arbitrary _, by simp, by simp⟩
  obtain ⟨κ, hκ⟩ : (L x₀).Nonempty :=
    Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hL x₀ hx₀))
  set S := U.filter (κ ∈ L ·) with hS
  obtain ⟨K, hKS, hKind, hKabs⟩ := hK S
  have hx₀S : x₀ ∈ S := by simp [hS, hx₀, hκ]
  have hKU : K ⊆ U := hKS.trans (filter_subset _ _)
  have hKne : K.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    by_cases hx : x₀ ∈ K
    · simp [h] at hx
    · obtain ⟨y, hy, -⟩ := hKabs x₀ hx₀S hx
      simp [h] at hy
  have hlt : (U \ K).card < n := by
    rw [← hn]
    exact Finset.card_lt_card (Finset.sdiff_ssubset hKU hKne)
  obtain ⟨c', hc'L, hc'p⟩ := ih _ hlt (U \ K) rfl (fun x => (L x).erase κ) (by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_cases hκx : κ ∈ L x
    · rw [Finset.card_erase_of_mem hκx]
      obtain ⟨y, hy, hD⟩ := hKabs x (by simp [hS, hx.1, hκx]) hx.2
      have hsub : insert y ((U \ K).filter (D x ·)) ⊆ U.filter (D x ·) := by
        intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · simp [hKU hy, hD]
        · simp only [Finset.mem_filter, Finset.mem_sdiff] at hz ⊢
          exact ⟨hz.1.1, hz.2⟩
      have hyn : y ∉ (U \ K).filter (D x ·) := by simp [hy]
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hyn] at this
      have := hL x hx.1
      omega
    · rw [Finset.erase_eq_of_notMem hκx]
      refine lt_of_le_of_lt (Finset.card_le_card ?_) (hL x hx.1)
      exact Finset.filter_subset_filter _ Finset.sdiff_subset)
  refine ⟨fun x => if x ∈ K then κ else c' x, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · by_cases hxK : x ∈ K
    · simp only [hxK, ite_true]
      have := hKS hxK
      simp only [hS, Finset.mem_filter] at this
      exact this.2
    · simp only [hxK, ite_false]
      exact Finset.mem_of_mem_erase (hc'L x (by simp [hx, hxK]))
  · by_cases hxK : x ∈ K <;> by_cases hyK : y ∈ K <;> simp only [hxK, hyK, ite_true, ite_false]
    · exact (hKind x hxK y hyK hxy).elim
    · intro h
      have := hc'L y (by simp [hy, hyK])
      rw [← h] at this
      simp at this
    · intro h
      have := hc'L x (by simp [hx, hxK])
      rw [h] at this
      simp at this
    · exact hc'p x (by simp [hx, hxK]) y (by simp [hy, hyK]) hxy
end Galvin
