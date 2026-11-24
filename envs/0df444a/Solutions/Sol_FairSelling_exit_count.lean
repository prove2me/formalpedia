-- Prove2me | solution 1 for FairSelling.exit_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:28.483369+00:00
-- url     : https://prove2.me/submissions/8ab444e4-bc99-4620-8d25-c387e994817d

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue
import Definitions.Def_RequestProject_TwoThirdsDescent

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (bg : ι → Finset G) (hbdisj : ∀ j j', j ≠ j' → Disjoint (bg j) (bg j'))
    (bidx : κ → ι) {J : Finset ι} {Q : Finset κ} {Lset : Finset G}
    (hQJ : ∀ b ∈ Q, bidx b ∈ J)
    (hLJ : ∀ g ∈ Lset, ∃ j ∈ J, g ∈ bg j)
    (h1 : ∀ j ∈ J, (Q.filter (fun b => bidx b = j)).card ≤ 1)
    (h2 : ∀ j ∈ J, (Lset.filter (fun g => g ∈ bg j)).card ≤ 1)
    (h3 : (J.filter (fun j => (Q.filter (fun b => bidx b = j)).Nonempty ∧
        (Lset.filter (fun g => g ∈ bg j)).Nonempty)).card ≤ 1) :
    Lset.card + Q.card ≤ J.card + 1 := by
  classical
  set Mixset : Finset ι := J.filter (fun j => (Q.filter (fun b => bidx b = j)).Nonempty ∧
      (Lset.filter (fun g => g ∈ bg j)).Nonempty) with hMixset
  have hQcard : Q.card = ∑ j ∈ J, (Q.filter (fun b => bidx b = j)).card := by
    have hQeq : Q = J.biUnion (fun j => Q.filter (fun b => bidx b = j)) := by
      ext b
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun hb => ⟨bidx b, hQJ b hb, hb, rfl⟩, fun ⟨_, _, hb, _⟩ => hb⟩
    conv_lhs => rw [hQeq]
    refine Finset.card_biUnion ?_
    intro x _ y _ hxy
    refine Finset.disjoint_left.mpr (fun b hb hb' => absurd ?_ hxy)
    rw [← (Finset.mem_filter.mp hb).2, (Finset.mem_filter.mp hb').2]
  have hLcard : Lset.card = ∑ j ∈ J, (Lset.filter (fun g => g ∈ bg j)).card := by
    have hLeq : Lset = J.biUnion (fun j => Lset.filter (fun g => g ∈ bg j)) := by
      ext g
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hg
        obtain ⟨j, hj, hgj⟩ := hLJ g hg
        exact ⟨j, hj, hg, hgj⟩
      · rintro ⟨_, _, hg, _⟩; exact hg
    conv_lhs => rw [hLeq]
    refine Finset.card_biUnion ?_
    intro x _ y _ hxy
    exact Finset.disjoint_left.mpr (fun g hg hg' =>
      Finset.disjoint_left.mp (hbdisj x y hxy) (Finset.mem_filter.mp hg).2
        (Finset.mem_filter.mp hg').2)
  have hbound : ∀ j ∈ J, (Lset.filter (fun g => g ∈ bg j)).card
      + (Q.filter (fun b => bidx b = j)).card ≤ 1 + (if j ∈ Mixset then 1 else 0) := by
    intro j hj
    by_cases hmem : j ∈ Mixset
    · rw [if_pos hmem]
      have := h1 j hj
      have := h2 j hj
      omega
    · rw [if_neg hmem]
      rw [hMixset] at hmem
      have hnot : ¬ ((Q.filter (fun b => bidx b = j)).Nonempty ∧
          (Lset.filter (fun g => g ∈ bg j)).Nonempty) := by
        intro hcon
        exact hmem (Finset.mem_filter.mpr ⟨hj, hcon⟩)
      rcases not_and_or.mp hnot with hcon | hcon
      · have : (Q.filter (fun b => bidx b = j)).card = 0 :=
          Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hcon)
        have := h2 j hj
        omega
      · have : (Lset.filter (fun g => g ∈ bg j)).card = 0 :=
          Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hcon)
        have := h1 j hj
        omega
  have hMixsub : Mixset ⊆ J := by rw [hMixset]; exact Finset.filter_subset _ _
  have hite : ∑ j ∈ J, (if j ∈ Mixset then 1 else 0) = Mixset.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hMixsub, Finset.card_eq_sum_ones]
  calc Lset.card + Q.card
      = ∑ j ∈ J, ((Lset.filter (fun g => g ∈ bg j)).card
          + (Q.filter (fun b => bidx b = j)).card) := by
        rw [Finset.sum_add_distrib, ← hLcard, ← hQcard]
    _ ≤ ∑ j ∈ J, (1 + (if j ∈ Mixset then 1 else 0)) := Finset.sum_le_sum hbound
    _ = J.card + Mixset.card := by rw [Finset.sum_add_distrib, hite]; simp
    _ ≤ J.card + 1 := by omega
end FairSelling
