-- Prove2me | solution 1 for AutoregLTF.lemma_2_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:59.222953+00:00
-- url     : https://prove2.me/submissions/19541e93-1a70-4ba3-a63e-7265589260a9

import Mathlib
import Definitions.Def_AutoregLTF_coef

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Claim1
open AutoregLTF

lemma mem_assign0 (m : ℕ) (θ : ℕ → ℤ) (e : ℤ × ℤ) :
    e ∈ assign0 m θ ↔ ∃ j, (1 ≤ j ∧ j ≤ m) ∧ e ∈ assign0At m θ j := by
  simp only [assign0, List.mem_flatMap, List.mem_range'_1]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, h⟩; exact ⟨j, ⟨h1, by omega⟩, h⟩
  · rintro ⟨j, ⟨h1, h2⟩, h⟩; exact ⟨j, ⟨h1, by omega⟩, h⟩

/-- the eleven pairs, unpacked. -/
lemma mem_assign0At (m : ℕ) (θ : ℕ → ℤ) (j : ℕ) (e : ℤ × ℤ) :
    e ∈ assign0At m θ j ↔
      e = ((p m : ℤ) + (piTest m : ℤ) - (piRow m j : ℤ), 4 * θ j) ∨
      e = ((p m : ℤ) + (piTest m : ℤ) - (piOut m j : ℤ), -(2 ^ (j + 1))) ∨
      e = ((p m : ℤ) + (piTest m : ℤ) - (piPtr m j : ℤ), -(2 ^ (j + 1))) ∨
      e = ((piOut m j : ℤ) - (piTest m : ℤ), 1) ∨
      e = ((p m : ℤ) + (piOut m j : ℤ) - (piPtr m j : ℤ), 1) ∨
      e = ((p m : ℤ) + (piPtr m j : ℤ) - (piPtr m (j + 1) : ℤ), 4) ∨
      e = ((p m : ℤ) + (piTest m : ℤ) - (piOut m j : ℤ) + 1, 2 ^ (j + 1)) ∨
      e = ((p m : ℤ) + (piTest m : ℤ) - (piPtr m j : ℤ) + 1, 2 ^ (j + 1)) ∨
      e = ((piOut m j : ℤ) - (piTest m : ℤ) + 1, -1) ∨
      e = ((p m : ℤ) + (piOut m j : ℤ) - (piPtr m j : ℤ) + 1, -1) ∨
      e = ((p m : ℤ) + (piPtr m j : ℤ) - (piPtr m (j + 1) : ℤ) + 1, -4) := by
  simp [assign0At]


/-- membership in `assignUpd`, unpacked. -/
lemma mem_upd (m : ℕ) (e : ℤ × ℤ) :
    e ∈ assignUpd m ↔
      (e = (1, 2) ∨ e = ((p m : ℤ) - 1, 1 - Bconst m) ∨ e = ((p m : ℤ), Bconst m + 1) ∨
        e = ((p m : ℤ) + 1, -Bconst m - 1) ∨ e = ((piTest m : ℤ), Bconst m + 1) ∨
        e = ((piTest m : ℤ) + 1, Bconst m - 1)) ∨
      (∃ j, (1 ≤ j ∧ j ≤ m) ∧
        (e = ((piOut m j : ℤ), Bconst m - 2) ∨ e = ((piOut m j : ℤ) + 1, Bconst m - 1))) ∨
      (∃ j, (1 ≤ j ∧ j ≤ m + 1) ∧
        (e = ((piPtr m j : ℤ), Bconst m - 3) ∨ e = ((piPtr m j : ℤ) + 1, Bconst m - 1))) ∨
      (∃ n : ℕ, (p m / 3 + 1 ≤ n ∧ n < p m / 3 + 1 + p m / 3) ∧ e = ((n : ℤ), -Bconst m ^ 2)) := by
  simp only [assignUpd, List.pure_def, List.bind_eq_flatMap, List.mem_append, List.mem_flatMap, List.mem_range'_1,
    List.mem_map, List.mem_cons, List.not_mem_nil, or_false, List.mem_singleton]
  constructor
  · rintro (((h | ⟨a, ⟨h1, h2⟩, h⟩) | ⟨a, ⟨h1, h2⟩, h⟩) | ⟨a, ⟨n, ⟨h1, h2⟩, hn⟩, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, ⟨h1, by omega⟩, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, ⟨h1, by omega⟩, h⟩))
    · subst hn; exact Or.inr (Or.inr (Or.inr ⟨n, ⟨h1, h2⟩, h.symm⟩))
  · rintro (h | ⟨a, ⟨h1, h2⟩, h⟩ | ⟨a, ⟨h1, h2⟩, h⟩ | ⟨n, ⟨h1, h2⟩, h⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨a, ⟨h1, by omega⟩, h⟩))
    · exact Or.inl (Or.inr ⟨a, ⟨h1, by omega⟩, h⟩)
    · exact Or.inr ⟨(n : ℤ), ⟨n, ⟨h1, h2⟩, rfl⟩, h.symm⟩

lemma upd_range (m : ℕ) (hm : 2 ≤ m) (e : ℤ × ℤ) (he : e ∈ assignUpd m) :
    1 ≤ e.1 ∧ e.1 ≤ (p m : ℤ) + 1 := by
  rw [mem_upd] at he
  simp only [p, piTest, piOut, piPtr] at he ⊢
  rcases he with h | ⟨j, ⟨h1, h2⟩, h⟩ | ⟨j, ⟨h1, h2⟩, h⟩ | ⟨n, ⟨h1, h2⟩, h⟩
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> (dsimp only; push_cast; refine ⟨?_, ?_⟩ <;> first | omega | trivial)
  · rcases h with rfl|rfl <;> (dsimp only; push_cast; refine ⟨?_, ?_⟩ <;> first | omega | trivial)
  · rcases h with rfl|rfl <;> (dsimp only; push_cast; refine ⟨?_, ?_⟩ <;> first | omega | trivial)
  · subst h; push_cast; constructor <;> omega

set_option maxHeartbeats 2000000 in
lemma upd_disj (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (e e' : ℤ × ℤ) (he : e ∈ assignUpd m)
    (he' : e' ∈ assign0 m θ) : e.1 ≠ e'.1 := by
  rw [mem_upd] at he
  obtain ⟨j', ⟨h1', h2'⟩, he'⟩ := (mem_assign0 m θ e').1 he'
  rw [mem_assign0At] at he'
  simp only [p, piTest, piRow, piOut, piPtr] at he he'
  rcases he' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  rcases he with h | ⟨j, ⟨h1, h2⟩, h⟩ | ⟨j, ⟨h1, h2⟩, h⟩ | ⟨n, ⟨h1, h2⟩, h⟩ <;>
  (try rcases h with rfl|rfl|rfl|rfl|rfl|rfl) <;>
  simp only <;> push_cast <;> omega

lemma upd_nodup (m : ℕ) (hm : 2 ≤ m) : ((assignUpd m).map Prod.fst).Nodup := by
  simp only [assignUpd, List.pure_def, List.bind_eq_flatMap, List.map_append, List.map_flatMap,
    List.nodup_append, List.nodup_flatMap]
  refine ⟨⟨⟨?_, ⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · simp only [p, piTest]; simp; omega
  · intro x hx; simp
  · refine (List.pairwise_lt_range' (s := 1) (n := m)).imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left]
    intro x h1 h2
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at h1 h2
    simp only [piOut, p] at h1 h2
    omega
  · intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_range'_1] at ha hb
    obtain ⟨j, ⟨h1, h2⟩, hb⟩ := hb
    try simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
    simp only [piOut, piTest, p] at ha hb
    intro hab
    rcases ha with ha|ha|ha|ha|ha|ha <;> rcases hb with hb|hb <;> omega
  · intro x _; simp
  · refine (List.pairwise_lt_range' (s := 1) (n := m + 1)).imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left]
    intro x h1 h2
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at h1 h2
    simp only [piPtr, p] at h1 h2
    omega
  · intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_range'_1, List.mem_append] at ha hb
    obtain ⟨j, ⟨h1, h2⟩, hb⟩ := hb
    try simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
    simp only [piOut, piPtr, piTest, p] at ha hb
    intro hab
    rcases ha with (ha|ha|ha|ha|ha|ha) | ⟨i, ⟨h3, h4⟩, ha|ha⟩ <;>
      rcases hb with hb|hb <;> omega
  · refine ⟨fun x _ => by simp, ?_⟩
    refine (List.pairwise_lt_range' (s := p m / 3 + 1) (n := p m / 3)).imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left]
    intro x h1 h2
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at h1 h2
    omega
  · intro a ha b hb
    simp only [List.mem_flatMap, List.mem_range'_1, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_append] at ha hb
    obtain ⟨n, ⟨h1, h2⟩, hb⟩ := hb
    intro hab
    simp only [piOut, piPtr, piTest, p] at ha h1 h2
    subst hb
    rcases ha with ((ha|ha|ha|ha|ha|ha) | ⟨i, ⟨h3, h4⟩, ha|ha⟩) | ⟨i, ⟨h3, h4⟩, ha|ha⟩ <;>
      omega


end AutoregLTF.Dev.Claim1

namespace AutoregLTF
open AutoregLTF.Dev.Claim1

end AutoregLTF
end

section
set_option autoImplicit false
namespace AutoregLTF
open AutoregLTF.Dev.Claim1

theorem chk_lemma_2_disjoint (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) :
    ((assignUpd m).map Prod.fst).Nodup ∧
    (∀ e ∈ assignUpd m, 1 ≤ e.1 ∧ e.1 ≤ (p m : ℤ) + 1) ∧
    ∀ e ∈ assignUpd m, ∀ e' ∈ assign0 m θ, e.1 ≠ e'.1 :=
  ⟨upd_nodup m hm, fun e he => upd_range m hm e he, fun e he e' he' => upd_disj m hm θ e e' he he'⟩

end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_lemma_2_disjoint := @AutoregLTF.chk_lemma_2_disjoint
