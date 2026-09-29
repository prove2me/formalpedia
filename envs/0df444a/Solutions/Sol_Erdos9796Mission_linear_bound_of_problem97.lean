-- Prove2me | solution 1 for Erdos9796Mission.linear_bound_of_problem97
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-07T22:42:06.893214+00:00
-- url     : https://prove2.me/submissions/babc821b-786f-4c21-8fea-e237eb0030e7

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Erdos9796Mission
set_option autoImplicit false
open Finset Filter
open Erdos9796Mission

namespace Erdos9796Bridge

noncomputable def unitPair (s : Sym2 Plane) : Prop :=
  Sym2.lift ⟨fun p q : Plane ↦ 0 < dist p q ∧ dist p q = 1,
    fun p q ↦ congrArg (fun d : ℝ ↦ 0 < d ∧ d = 1) (dist_comm p q)⟩ s

lemma count_erase (A : Finset Plane) (p : Plane) (hp : p ∈ A) :
    unitDistancePairsCount A ≤ unitDistancePairsCount (A.erase p) +
      (A.filter fun q ↦ dist p q = 1).card := by
  classical
  change (A.sym2.filter unitPair).card ≤ ((A.erase p).sym2.filter unitPair).card + _
  have hs : A.sym2 = (A.image fun q ↦ s(p, q)) ∪ (A.erase p).sym2 := by
    conv_lhs => rw [← insert_erase hp]
    rw [sym2_insert, insert_erase hp]
  have hf : (A.image fun q ↦ s(p, q)).filter unitPair =
      (A.filter fun q ↦ dist p q = 1).image (fun q ↦ s(p, q)) := by
    ext e
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, h⟩
      exact ⟨q, ⟨hq, h.2⟩, rfl⟩
    · rintro ⟨q, ⟨hq, hd⟩, rfl⟩
      exact ⟨⟨q, hq, rfl⟩, by
        change 0 < dist p q ∧ dist p q = 1
        rw [hd]
        norm_num⟩
  rw [hs, filter_union, hf]
  exact (card_union_le _ _).trans (by
    have h := card_image_le (s := A.filter fun q ↦ dist p q = 1) (f := fun q ↦ s(p, q))
    omega)

lemma convex_erase {A : Finset Plane} (h : ConvexIndep (A : Set Plane)) (p : Plane) :
    ConvexIndep (A.erase p : Set Plane) := by
  intro a ha hm
  exact h a (erase_subset p A ha)
    (convexHull_mono (Set.sdiff_subset_sdiff_left (coe_subset.mpr (erase_subset p A))) hm)

lemma low_degree (hP97 : Problem97) {A : Finset Plane} (hne : A.Nonempty)
    (hconv : ConvexIndep (A : Set Plane)) :
    ∃ p ∈ A, (A.filter fun q ↦ dist p q = 1).card ≤ 3 := by
  classical
  have h := hP97 A hne hconv
  unfold HasNEquidistantProperty HasNEquidistantPointsOn HasNEquidistantPointsAt at h
  push Not at h
  obtain ⟨p, hp, hd⟩ := h
  exact ⟨p, hp, by have := hd 1 (by norm_num); omega⟩

lemma per_set_bound (hP97 : Problem97) (A : Finset Plane)
    (hconv : ConvexIndep (A : Set Plane)) : unitDistancePairsCount A ≤ 3 * A.card := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hne : A.Nonempty
    · obtain ⟨p, hp, hd⟩ := low_degree hP97 hne hconv
      have hi := ih (A.erase p) (erase_ssubset hp) (convex_erase hconv p)
      have hc := count_erase A p hp
      have he := card_erase_of_mem hp
      have hpos : 0 < A.card := card_pos.mpr hne
      omega
    · have he : A = ∅ := not_nonempty_iff_eq_empty.mp hne
      simp [he, unitDistancePairsCount]

lemma supremum_bound (hP97 : Problem97) (n : ℕ) : maxConvexUnitDistances n ≤ 3 * n := by
  unfold maxConvexUnitDistances
  rcases Set.eq_empty_or_nonempty (convexUnitDistanceCounts n) with h | h
  · rw [h, csSup_empty]
    exact bot_le
  · refine csSup_le h ?_
    rintro x ⟨A, hcard, hconv, rfl⟩
    simpa [hcard] using per_set_bound hP97 A hconv

end Erdos9796Bridge

theorem solution :
    Problem97 → (∀ A : Finset Plane, ConvexIndep (A : Set Plane) →
      unitDistancePairsCount A ≤ 3 * A.card) ∧ Problem96 := by
  intro hP97
  refine ⟨Erdos9796Bridge.per_set_bound hP97, ?_⟩
  refine Asymptotics.isBigO_of_le' (c := 3) atTop fun n ↦ ?_
  rw [Real.norm_natCast, Real.norm_natCast]
  exact_mod_cast Erdos9796Bridge.supremum_bound hP97 n
