-- Prove2me | solution 1 for AutoregLTF.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:19:46.416183+00:00
-- url     : https://prove2.me/submissions/108a480f-214f-47f2-a8ec-9a60bd75ba03

import Mathlib
import Definitions.Def_AutoregLTF_coef
import Definitions.Def_AutoregLTF_sigma

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

lemma claim1_range (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (e : ℤ × ℤ) (he : e ∈ assign0 m θ) :
    1 ≤ e.1 ∧ e.1 ≤ (p m : ℤ) + 1 := by
  obtain ⟨j, ⟨h1, h2⟩, he⟩ := (mem_assign0 m θ e).1 he
  rw [mem_assign0At] at he
  simp only [p, piTest, piRow, piOut, piPtr] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [p]; push_cast; constructor <;> omega)

set_option maxHeartbeats 2000000 in
lemma claim1_cons (m : ℕ) (θ : ℕ → ℤ) (e e' : ℤ × ℤ)
    (he : e ∈ assign0 m θ) (he' : e' ∈ assign0 m θ) (h : e'.1 = e.1) : e'.2 = e.2 := by
  obtain ⟨j, ⟨h1, h2⟩, he⟩ := (mem_assign0 m θ e).1 he
  obtain ⟨j', ⟨h1', h2'⟩, he'⟩ := (mem_assign0 m θ e').1 he'
  rw [mem_assign0At] at he he'
  simp only [p, piTest, piRow, piOut, piPtr] at he he'
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  rcases he' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  simp only at h ⊢ <;> push_cast at h ⊢ <;>
  first
    | (exfalso; omega)
    | rfl
    | (obtain rfl : j' = j := by omega
       rfl)


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


lemma beq_false_of_ne (a ℓ : ℤ) (ha : a ≠ ℓ) : (ℓ == a) = false := by
  rw [beq_eq_false_iff_ne]; exact fun h => ha h.symm

lemma lookup_of_mem (l : List (ℤ × ℤ)) (ℓ v : ℤ) (hmem : (ℓ, v) ∈ l)
    (hc : ∀ e ∈ l, e.1 = ℓ → e.2 = v) : l.lookup ℓ = some v := by
  induction l with
  | nil => simp at hmem
  | cons x t ih =>
    obtain ⟨a, b⟩ := x
    by_cases ha : a = ℓ
    · subst ha
      have := hc (a, b) (List.mem_cons_self) rfl
      simpa [List.lookup] using this
    · simp only [List.lookup, beq_false_of_ne a ℓ ha]
      refine ih ?_ (fun e he => hc e (List.mem_cons_of_mem _ he))
      rcases List.mem_cons.1 hmem with h | h
      · exact absurd (congrArg Prod.fst h).symm ha
      · exact h

lemma lookup_none (l : List (ℤ × ℤ)) (ℓ : ℤ) (h : ∀ e ∈ l, e.1 ≠ ℓ) : l.lookup ℓ = none := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨a, b⟩ := x
    have ha : a ≠ ℓ := h (a, b) List.mem_cons_self
    simp only [List.lookup, beq_false_of_ne a ℓ ha]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

lemma key_unique (l : List (ℤ × ℤ)) (hl : (l.map Prod.fst).Nodup) (a b c : ℤ)
    (hb : (a, b) ∈ l) (hc : (a, c) ∈ l) : b = c := by
  induction l with
  | nil => simp at hb
  | cons x t ih =>
    obtain ⟨x1, x2⟩ := x
    rw [List.map_cons, List.nodup_cons] at hl
    rcases List.mem_cons.1 hb with h | h <;> rcases List.mem_cons.1 hc with h' | h'
    · rw [Prod.mk.injEq] at h h'; rw [h.2, h'.2]
    · exfalso; rw [Prod.mk.injEq] at h; exact hl.1 (List.mem_map.2 ⟨_, h', by simp [h.1]⟩)
    · exfalso; rw [Prod.mk.injEq] at h'; exact hl.1 (List.mem_map.2 ⟨_, h, by simp [h'.1]⟩)
    · exact ih hl.2 h h'

lemma lookup_upd (m : ℕ) (hm : 2 ≤ m) (ℓ v : ℤ) (hmem : (ℓ, v) ∈ assignUpd m) :
    (assignUpd m).lookup ℓ = some v :=
  lookup_of_mem _ ℓ v hmem (fun e he hℓ => by
    have : e = (e.1, e.2) := rfl
    rw [this, hℓ] at he
    exact key_unique _ (upd_nodup m hm) ℓ _ _ he hmem)

lemma lookup_assign0 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (ℓ v : ℤ) (hmem : (ℓ, v) ∈ assign0 m θ) :
    (assign0 m θ).lookup ℓ = some v :=
  lookup_of_mem _ ℓ v hmem (fun e he hℓ => claim1_cons m θ (ℓ, v) e hmem he hℓ)

end AutoregLTF.Dev.Claim1

namespace AutoregLTF
open AutoregLTF.Dev.Claim1

theorem aCoef_of_mem_assign0 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ v : ℤ)
    (hmem : (ℓ, v) ∈ assign0 m θ) : aCoef m θ ℓ = v := by
  have hn : (assignUpd m).lookup ℓ = none :=
    lookup_none _ _ (fun e he h => upd_disj m hm θ e (ℓ, v) he hmem h)
  simp [aCoef, hn, a0, lookup_assign0 m hm θ ℓ v hmem]

theorem aCoef_of_mem_assignUpd (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ v : ℤ)
    (hmem : (ℓ, v) ∈ assignUpd m) : aCoef m θ ℓ = v := by
  simp [aCoef, lookup_upd m hm ℓ v hmem]

theorem aCoef_zero_of_not_mem (m : ℕ) (θ : ℕ → ℤ) (ℓ : ℤ)
    (h0 : ∀ e ∈ assign0 m θ, e.1 ≠ ℓ) (h1 : ∀ e ∈ assignUpd m, e.1 ≠ ℓ) :
    aCoef m θ ℓ = 0 := by
  simp [aCoef, lookup_none _ _ h1, a0, lookup_none _ _ h0]

end AutoregLTF
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace AutoregLTF.Dev.Claim2
open AutoregLTF AutoregLTF.Dev.Claim1

lemma p_int (m : ℕ) : (p m : ℤ) = 378 * (m + 2) := by
  simp only [p]; push_cast; ring

lemma pT_int (m : ℕ) : (piTest m : ℤ) = 63 * m + 129 := by
  simp only [piTest, p]; omega

lemma pR_int (m j : ℕ) : (piRow m j : ℤ) = 63 * m + 132 + 63 * j := by
  simp only [piRow, p]; omega

lemma pO_int (m j : ℕ) : (piOut m j : ℤ) = 63 * m + 141 + 63 * j := by
  simp only [piOut, p]; omega

lemma pP_int (m j : ℕ) : (piPtr m j : ℤ) = 63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2) := by
  simp only [piPtr, p]; omega

lemma p3_int (m : ℕ) : ((p m / 3 : ℕ) : ℤ) = 126 * m + 252 := by
  simp only [p]; omega

/-- `a_ℓ = 0` unless `ℓ` is one of the listed indices of (17), (18), (22), (23). -/
lemma a_zero (m : ℕ) (θ : ℕ → ℤ) (ℓ : ℤ)
    (h0 : ℓ ≠ 1 ∧ ℓ ≠ 378 * (m + 2) - 1 ∧ ℓ ≠ 378 * (m + 2) ∧ ℓ ≠ 378 * (m + 2) + 1 ∧
      ℓ ≠ 63 * m + 129 ∧ ℓ ≠ 63 * m + 130 ∧ ¬ (126 * m + 253 ≤ ℓ ∧ ℓ ≤ 252 * m + 504))
    (h1 : ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 →
      ℓ ≠ 63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2) ∧
      ℓ ≠ 63 * m + 172 + 63 * j + 6 * ((j : ℤ) % 2) ∧
      (j ≤ m → ℓ ≠ 63 * m + 141 + 63 * j ∧ ℓ ≠ 63 * m + 142 + 63 * j ∧
        ℓ ≠ 378 * (m + 2) + (63 * m + 129) - (63 * m + 132 + 63 * j) ∧
        ℓ ≠ 378 * (m + 2) + (63 * m + 129) - (63 * m + 141 + 63 * j) ∧
        ℓ ≠ 378 * (m + 2) + (63 * m + 129) - (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) ∧
        ℓ ≠ (63 * m + 141 + 63 * j) - (63 * m + 129) ∧
        ℓ ≠ 378 * (m + 2) + (63 * m + 141 + 63 * j) -
            (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) ∧
        ℓ ≠ 378 * (m + 2) + (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) -
            (63 * m + 171 + 63 * (j + 1) + 6 * (((j + 1 : ℕ) : ℤ) % 2)) ∧
        ℓ ≠ 378 * (m + 2) + (63 * m + 129) - (63 * m + 141 + 63 * j) + 1 ∧
        ℓ ≠ 378 * (m + 2) + (63 * m + 129) - (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) + 1 ∧
        ℓ ≠ (63 * m + 141 + 63 * j) - (63 * m + 129) + 1 ∧
        ℓ ≠ 378 * (m + 2) + (63 * m + 141 + 63 * j) -
            (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) + 1 ∧
        ℓ ≠ 378 * (m + 2) + (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) -
            (63 * m + 171 + 63 * (j + 1) + 6 * (((j + 1 : ℕ) : ℤ) % 2)) + 1)) :
    aCoef m θ ℓ = 0 := by
  apply aCoef_zero_of_not_mem
  · intro e he hel
    obtain ⟨j, ⟨hj1, hj2⟩, he⟩ := (mem_assign0 m θ e).1 he
    have := (h1 j hj1 (by omega)).2.2 hj2
    rw [mem_assign0At] at he
    simp only [p_int, pT_int, pR_int, pO_int, pP_int] at he
    push_cast at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only at hel <;> omega
  · intro e he hel
    rw [mem_upd] at he
    simp only [p_int, pT_int, pO_int, pP_int, p3_int, Bconst] at he
    rcases he with h | ⟨j, ⟨hj1, hj2⟩, h⟩ | ⟨j, ⟨hj1, hj2⟩, h⟩ | ⟨n, ⟨hn1, hn2⟩, h⟩
    · rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only at hel <;> omega
    · have := h1 j hj1 (by omega)
      rcases h with rfl|rfl <;> simp only at hel <;> omega
    · have := h1 j hj1 hj2
      rcases h with rfl|rfl <;> simp only at hel <;> omega
    · subst h; simp only [p] at hn1 hn2; simp only at hel; omega

lemma a17a (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 378 * (m + 2) + (63 * m + 129) - (63 * m + 132 + 63 * j)) :
    aCoef m θ ℓ = 4 * θ j := by
  have e : ℓ = (p m : ℤ) + piTest m - piRow m j := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a17b (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 378 * (m + 2) + (63 * m + 129) - (63 * m + 141 + 63 * j)) :
    aCoef m θ ℓ = -(2 ^ (j + 1)) := by
  have e : ℓ = (p m : ℤ) + piTest m - piOut m j := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a17c (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 378 * (m + 2) + (63 * m + 129) - (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2))) :
    aCoef m θ ℓ = -(2 ^ (j + 1)) := by
  have e : ℓ = (p m : ℤ) + piTest m - piPtr m j := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a17d (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = (63 * m + 141 + 63 * j) - (63 * m + 129)) :
    aCoef m θ ℓ = 1 := by
  have e : ℓ = (piOut m j : ℤ) - piTest m := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a17e (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 378 * (m + 2) + (63 * m + 141 + 63 * j) - (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2))) :
    aCoef m θ ℓ = 1 := by
  have e : ℓ = (p m : ℤ) + piOut m j - piPtr m j := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a17f (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 378 * (m + 2) + (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) - (63 * m + 171 + 63 * (j + 1) + 6 * (((j + 1 : ℕ) : ℤ) % 2))) :
    aCoef m θ ℓ = 4 := by
  have e : ℓ = (p m : ℤ) + piPtr m j - piPtr m (j + 1) := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a18b (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 378 * (m + 2) + (63 * m + 129) - (63 * m + 141 + 63 * j) + 1) :
    aCoef m θ ℓ = 2 ^ (j + 1) := by
  have e : ℓ = (p m : ℤ) + piTest m - piOut m j + 1 := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a18c (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 378 * (m + 2) + (63 * m + 129) - (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) + 1) :
    aCoef m θ ℓ = 2 ^ (j + 1) := by
  have e : ℓ = (p m : ℤ) + piTest m - piPtr m j + 1 := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a18d (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = (63 * m + 141 + 63 * j) - (63 * m + 129) + 1) :
    aCoef m θ ℓ = -1 := by
  have e : ℓ = (piOut m j : ℤ) - piTest m + 1 := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a18e (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 378 * (m + 2) + (63 * m + 141 + 63 * j) - (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) + 1) :
    aCoef m θ ℓ = -1 := by
  have e : ℓ = (p m : ℤ) + piOut m j - piPtr m j + 1 := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a18f (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ)
    (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 378 * (m + 2) + (63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) - (63 * m + 171 + 63 * (j + 1) + 6 * (((j + 1 : ℕ) : ℤ) % 2)) + 1) :
    aCoef m θ ℓ = -4 := by
  have e : ℓ = (p m : ℤ) + piPtr m j - piPtr m (j + 1) + 1 := by
    rw [h]; simp only [p_int, pT_int, pR_int, pO_int, pP_int] <;> omega
  rw [e]
  exact aCoef_of_mem_assign0 m hm θ hθ _ _
    ((mem_assign0 m θ _).2 ⟨j, hj, by simp [assign0At]⟩)

lemma a_upd (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ v : ℤ)
    (h : (ℓ, v) ∈ assignUpd m) : aCoef m θ ℓ = v :=
  aCoef_of_mem_assignUpd m hm θ hθ ℓ v h

lemma a_one (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (h : ℓ = 1) :
    aCoef m θ ℓ = 2 := by
  have e : ℓ = (1 : ℤ) := h
  rw [e]
  exact a_upd m hm θ hθ _ _ ((mem_upd m _).2 (Or.inl (Or.inl rfl)))

lemma a_pm1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (h : ℓ = 378 * (m + 2) - 1) :
    aCoef m θ ℓ = 1 - Bconst m := by
  have e : ℓ = (p m : ℤ) - 1 := by
    rw [h]; simp only [p_int, pT_int, pO_int, pP_int] <;> omega
  rw [e]
  exact a_upd m hm θ hθ _ _ ((mem_upd m _).2 (Or.inl (Or.inr (Or.inl rfl))))

lemma a_p0 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (h : ℓ = 378 * (m + 2)) :
    aCoef m θ ℓ = Bconst m + 1 := by
  have e : ℓ = (p m : ℤ) := by
    rw [h]; simp only [p_int, pT_int, pO_int, pP_int] <;> omega
  rw [e]
  exact a_upd m hm θ hθ _ _ ((mem_upd m _).2 (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))

lemma a_pp1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (h : ℓ = 378 * (m + 2) + 1) :
    aCoef m θ ℓ = -Bconst m - 1 := by
  have e : ℓ = (p m : ℤ) + 1 := by
    rw [h]; simp only [p_int, pT_int, pO_int, pP_int] <;> omega
  rw [e]
  exact a_upd m hm θ hθ _ _ ((mem_upd m _).2 (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

lemma a_T0 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (h : ℓ = 63 * m + 129) :
    aCoef m θ ℓ = Bconst m + 1 := by
  have e : ℓ = (piTest m : ℤ) := by
    rw [h]; simp only [p_int, pT_int, pO_int, pP_int] <;> omega
  rw [e]
  exact a_upd m hm θ hθ _ _ ((mem_upd m _).2 (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))

lemma a_T1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (h : ℓ = 63 * m + 130) :
    aCoef m θ ℓ = Bconst m - 1 := by
  have e : ℓ = (piTest m : ℤ) + 1 := by
    rw [h]; simp only [p_int, pT_int, pO_int, pP_int] <;> omega
  rw [e]
  exact a_upd m hm θ hθ _ _ ((mem_upd m _).2 (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))

lemma a_O0 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 63 * m + 141 + 63 * j) :
    aCoef m θ ℓ = Bconst m - 2 := by
  have e : ℓ = (piOut m j : ℤ) := by
    rw [h]; simp only [p_int, pT_int, pO_int, pP_int] <;> omega
  rw [e]
  exact a_upd m hm θ hθ _ _ ((mem_upd m _).2 (Or.inr (Or.inl ⟨j, hj, Or.inl rfl⟩)))

lemma a_O1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ m) (h : ℓ = 63 * m + 142 + 63 * j) :
    aCoef m θ ℓ = Bconst m - 1 := by
  have e : ℓ = (piOut m j : ℤ) + 1 := by
    rw [h]; simp only [p_int, pT_int, pO_int, pP_int] <;> omega
  rw [e]
  exact a_upd m hm θ hθ _ _ ((mem_upd m _).2 (Or.inr (Or.inl ⟨j, hj, Or.inr rfl⟩)))

lemma a_P0 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ m + 1) (h : ℓ = 63 * m + 171 + 63 * j + 6 * ((j : ℤ) % 2)) :
    aCoef m θ ℓ = Bconst m - 3 := by
  have e : ℓ = (piPtr m j : ℤ) := by
    rw [h]; simp only [p_int, pT_int, pO_int, pP_int] <;> omega
  rw [e]
  exact a_upd m hm θ hθ _ _ ((mem_upd m _).2 (Or.inr (Or.inr (Or.inl ⟨j, hj, Or.inl rfl⟩))))

lemma a_P1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ : ℤ) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ m + 1) (h : ℓ = 63 * m + 172 + 63 * j + 6 * ((j : ℤ) % 2)) :
    aCoef m θ ℓ = Bconst m - 1 := by
  have e : ℓ = (piPtr m j : ℤ) + 1 := by
    rw [h]; simp only [p_int, pT_int, pO_int, pP_int] <;> omega
  rw [e]
  exact a_upd m hm θ hθ _ _ ((mem_upd m _).2 (Or.inr (Or.inr (Or.inl ⟨j, hj, Or.inr rfl⟩))))


/-- small indices: only `ℓ = 1` and the (17d), (18d) indices `63j + 12`, `63j + 13` are assigned -/
lemma a_zS (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (ℓ : ℤ)
    (h : ℓ ≤ 0 ∨ (2 ≤ ℓ ∧ ℓ ≤ 63 * m + 128 ∧
      (63 * m + 14 ≤ ℓ ∨ (ℓ % 63 ≠ 12 ∧ ℓ % 63 ≠ 13)))) : aCoef m θ ℓ = 0 := by
  apply aCoef_zero_of_not_mem
  · intro e he hel
    obtain ⟨j, ⟨hj1, hj2⟩, he⟩ := (mem_assign0 m θ e).1 he
    rw [mem_assign0At] at he
    simp only [p_int, pT_int, pR_int, pO_int, pP_int] at he
    push_cast at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only at hel <;>
      (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> omega)
  · intro e he hel
    rw [mem_upd] at he
    simp only [p_int, pT_int, pO_int, pP_int, Bconst] at he
    rcases he with h' | ⟨j, ⟨hj1, hj2⟩, h'⟩ | ⟨j, ⟨hj1, hj2⟩, h'⟩ | ⟨n, ⟨hn1, hn2⟩, h'⟩
    · rcases h' with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only at hel <;> omega
    · rcases h' with rfl|rfl <;> simp only at hel <;> omega
    · rcases h' with rfl|rfl <;> simp only at hel <;>
        (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> omega)
    · subst h'; simp only [p] at hn1 hn2; simp only at hel; omega

/-- the indices `π(b)`, `π(b) + 1` lie in the middle zone -/
lemma a_zM (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (ℓ : ℤ)
    (h : 63 * m + 129 ≤ ℓ ∧ ℓ ≤ 126 * m + 252 ∧ ℓ % 63 ≠ 3 ∧ ℓ % 63 ≠ 4 ∧ ℓ % 63 ≠ 15 ∧
      ℓ % 63 ≠ 16 ∧ ℓ % 63 ≠ 45 ∧ ℓ % 63 ≠ 46 ∧ ℓ % 63 ≠ 51 ∧ ℓ % 63 ≠ 52) :
    aCoef m θ ℓ = 0 := by
  apply aCoef_zero_of_not_mem
  · intro e he hel
    obtain ⟨j, ⟨hj1, hj2⟩, he⟩ := (mem_assign0 m θ e).1 he
    rw [mem_assign0At] at he
    simp only [p_int, pT_int, pR_int, pO_int, pP_int] at he
    push_cast at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only at hel <;>
      (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> omega)
  · intro e he hel
    rw [mem_upd] at he
    simp only [p_int, pT_int, pO_int, pP_int, Bconst] at he
    rcases he with h' | ⟨j, ⟨hj1, hj2⟩, h'⟩ | ⟨j, ⟨hj1, hj2⟩, h'⟩ | ⟨n, ⟨hn1, hn2⟩, h'⟩
    · rcases h' with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only at hel <;> omega
    · rcases h' with rfl|rfl <;> simp only at hel <;> omega
    · rcases h' with rfl|rfl <;> simp only at hel <;>
        (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> omega)
    · subst h'; simp only [p] at hn1 hn2; simp only at hel; omega

/-- large indices: beyond `p + 1`, or (below `p - 63m - 48`) unassigned, or outside the residue
classes of (17)-(18) -/
lemma a_zL (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (ℓ : ℤ)
    (h : 378 * (m + 2) + 1 < ℓ ∨ (252 * m + 505 ≤ ℓ ∧ ℓ ≤ 378 * (m + 2) - 63 * m - 49) ∨
      (378 * (m + 2) - 63 * m - 48 ≤ ℓ ∧ ℓ ≤ 378 * (m + 2) + 1 ∧ ℓ ≠ 378 * (m + 2) - 1 ∧
        ℓ ≠ 378 * (m + 2) ∧ ℓ ≠ 378 * (m + 2) + 1 ∧
        ℓ % 63 ≠ 60 ∧ ℓ % 63 ≠ 51 ∧ ℓ % 63 ≠ 15 ∧ ℓ % 63 ≠ 21 ∧ ℓ % 63 ≠ 12 ∧ ℓ % 63 ≠ 27 ∧
        ℓ % 63 ≠ 33 ∧ ℓ % 63 ≠ 6 ∧ ℓ % 63 ≠ 57 ∧ ℓ % 63 ≠ 61 ∧ ℓ % 63 ≠ 52 ∧ ℓ % 63 ≠ 16 ∧
        ℓ % 63 ≠ 22 ∧ ℓ % 63 ≠ 13 ∧ ℓ % 63 ≠ 28 ∧ ℓ % 63 ≠ 34 ∧ ℓ % 63 ≠ 7 ∧ ℓ % 63 ≠ 58)) :
    aCoef m θ ℓ = 0 := by
  apply aCoef_zero_of_not_mem
  · intro e he hel
    obtain ⟨j, ⟨hj1, hj2⟩, he⟩ := (mem_assign0 m θ e).1 he
    rw [mem_assign0At] at he
    simp only [p_int, pT_int, pR_int, pO_int, pP_int] at he
    push_cast at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only at hel <;>
      (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> omega)
  · intro e he hel
    rw [mem_upd] at he
    simp only [p_int, pT_int, pO_int, pP_int, Bconst] at he
    rcases he with h' | ⟨j, ⟨hj1, hj2⟩, h'⟩ | ⟨j, ⟨hj1, hj2⟩, h'⟩ | ⟨n, ⟨hn1, hn2⟩, h'⟩
    · rcases h' with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only at hel <;> omega
    · rcases h' with rfl|rfl <;> simp only at hel <;> omega
    · rcases h' with rfl|rfl <;> simp only at hel <;>
        (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> omega)
    · subst h'; simp only [p] at hn1 hn2; simp only at hel; omega

lemma ne_qr {ℓ q r E qE rE : ℤ} (hℓ : ℓ = 63 * q + r) (hr0 : 0 ≤ r) (hr1 : r < 63)
    (hE : E = 63 * qE + rE) (h0 : 0 ≤ rE) (h1 : rE < 63) (h : r ≠ rE ∨ q ≠ qE) : ℓ ≠ E := by
  omega

/-- `a_zero` with the index given as `63 * q + r` and the exclusions stated on `(q, r)` -/
lemma a_zero2 (m : ℕ) (θ : ℕ → ℤ) (ℓ q r : ℤ) (hℓ : ℓ = 63 * q + r) (hr0 : 0 ≤ r) (hr1 : r < 63)
    (h0 : ℓ ≠ 1 ∧ ℓ ≠ 378 * (m + 2) - 1 ∧ ℓ ≠ 378 * (m + 2) ∧ ℓ ≠ 378 * (m + 2) + 1 ∧
      ℓ ≠ 63 * m + 129 ∧ ℓ ≠ 63 * m + 130 ∧ ¬ (126 * m + 253 ≤ ℓ ∧ ℓ ≤ 252 * m + 504))
    (h1 : ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 →
      ((j : ℤ) % 2 = 0 → (r ≠ 45 ∨ q ≠ (j : ℤ) + (m : ℤ) + 2) ∧
        (r ≠ 46 ∨ q ≠ (j : ℤ) + (m : ℤ) + 2) ∧
        (j ≤ m → (r ≠ 15 ∨ q ≠ (j : ℤ) + (m : ℤ) + 2) ∧
          (r ≠ 16 ∨ q ≠ (j : ℤ) + (m : ℤ) + 2) ∧
          (r ≠ 60 ∨ q ≠ -(j : ℤ) + 6 * (m : ℤ) + 11) ∧
          (r ≠ 51 ∨ q ≠ -(j : ℤ) + 6 * (m : ℤ) + 11) ∧
          (r ≠ 21 ∨ q ≠ -(j : ℤ) + 6 * (m : ℤ) + 11) ∧
          (r ≠ 12 ∨ q ≠ (j : ℤ)) ∧
          (r ≠ 33 ∨ q ≠ 6 * (m : ℤ) + 11) ∧
          (r ≠ 57 ∨ q ≠ 6 * (m : ℤ) + 10) ∧
          (r ≠ 52 ∨ q ≠ -(j : ℤ) + 6 * (m : ℤ) + 11) ∧
          (r ≠ 22 ∨ q ≠ -(j : ℤ) + 6 * (m : ℤ) + 11) ∧
          (r ≠ 13 ∨ q ≠ (j : ℤ)) ∧
          (r ≠ 34 ∨ q ≠ 6 * (m : ℤ) + 11) ∧
          (r ≠ 58 ∨ q ≠ 6 * (m : ℤ) + 10))) ∧
      ((j : ℤ) % 2 = 1 → (r ≠ 51 ∨ q ≠ (j : ℤ) + (m : ℤ) + 2) ∧
        (r ≠ 52 ∨ q ≠ (j : ℤ) + (m : ℤ) + 2) ∧
        (j ≤ m → (r ≠ 15 ∨ q ≠ (j : ℤ) + (m : ℤ) + 2) ∧
          (r ≠ 16 ∨ q ≠ (j : ℤ) + (m : ℤ) + 2) ∧
          (r ≠ 60 ∨ q ≠ -(j : ℤ) + 6 * (m : ℤ) + 11) ∧
          (r ≠ 51 ∨ q ≠ -(j : ℤ) + 6 * (m : ℤ) + 11) ∧
          (r ≠ 15 ∨ q ≠ -(j : ℤ) + 6 * (m : ℤ) + 11) ∧
          (r ≠ 12 ∨ q ≠ (j : ℤ)) ∧
          (r ≠ 27 ∨ q ≠ 6 * (m : ℤ) + 11) ∧
          (r ≠ 6 ∨ q ≠ 6 * (m : ℤ) + 11) ∧
          (r ≠ 52 ∨ q ≠ -(j : ℤ) + 6 * (m : ℤ) + 11) ∧
          (r ≠ 16 ∨ q ≠ -(j : ℤ) + 6 * (m : ℤ) + 11) ∧
          (r ≠ 13 ∨ q ≠ (j : ℤ)) ∧
          (r ≠ 28 ∨ q ≠ 6 * (m : ℤ) + 11) ∧
          (r ≠ 7 ∨ q ≠ 6 * (m : ℤ) + 11)))) :
    aCoef m θ ℓ = 0 := by
  refine a_zero m θ ℓ h0 (fun j h1' h2' => ?_)
  have hq1 : (((j + 1 : ℕ) : ℤ) % 2) = 1 - (j : ℤ) % 2 := by omega
  obtain ⟨H0, H1⟩ := h1 j h1' h2'
  rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq
  · obtain ⟨i1, i2, i3⟩ := H0 hq
    refine ⟨ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) i1, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) i2, fun hjm => ?_⟩
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := i3 hjm
    exact ⟨ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c1, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c2, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c3, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c4, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c5, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c6, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c7, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c8, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c9, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c10, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c11, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c12, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c13⟩
  · obtain ⟨i1, i2, i3⟩ := H1 hq
    refine ⟨ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) i1, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) i2, fun hjm => ?_⟩
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := i3 hjm
    exact ⟨ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c1, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c2, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c3, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c4, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c5, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c6, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c7, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c8, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c9, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c10, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c11, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c12, ne_qr hℓ hr0 hr1 (by (try simp only [hq, hq1]); ring) (by norm_num) (by norm_num) c13⟩


end AutoregLTF.Dev.Claim2
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace AutoregLTF.Dev.Claim2
open AutoregLTF

def sOut (m : ℕ) (f : St) (s : ℤ) : ℤ :=
  ∑ j ∈ Finset.Icc 1 m, ((if s = (piOut m j : ℤ) then ((f.out j).toNat : ℤ) else 0) +
    (if s = (piOut m j : ℤ) + 1 then ((f.out j).toNat : ℤ) else 0))

def sPtr (m : ℕ) (f : St) (s : ℤ) : ℤ :=
  ∑ j ∈ Finset.Icc 1 (m + 1), ((if s = (piPtr m j : ℤ) then ((f.ptr j).toNat : ℤ) else 0) +
    (if s = (piPtr m j : ℤ) + 1 then ((f.ptr j).toNat : ℤ) else 0))

/-- additive form of the block bit at position `s` (positions are pairwise distinct) -/
def bsum (m : ℕ) (f : St) (s : ℤ) : ℤ :=
  (if s = 0 then 1 else 0) +
  ∑ j ∈ Finset.Icc 1 m, (if s = (piRow m j : ℤ) then ((f.row j).toNat : ℤ) else 0) +
  ((if s = (piTest m : ℤ) then (f.test.toNat : ℤ) else 0) +
    (if s = (piTest m : ℤ) + 1 then (f.test.toNat : ℤ) else 0)) +
  sOut m f s + sPtr m f s

lemma block_true_iff (m : ℕ) (f : St) (s : ℕ) :
    block m f s = true ↔
      s = 0 ∨ (∃ j, (1 ≤ j ∧ j ≤ m) ∧ s = piRow m j ∧ f.row j = true) ∨
      ((s = piTest m ∨ s = piTest m + 1) ∧ f.test = true) ∨
      (∃ j, (1 ≤ j ∧ j ≤ m) ∧ (s = piOut m j ∨ s = piOut m j + 1) ∧ f.out j = true) ∨
      (∃ j, (1 ≤ j ∧ j ≤ m + 1) ∧ (s = piPtr m j ∨ s = piPtr m j + 1) ∧ f.ptr j = true) := by
  simp only [block, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range'_1]
  constructor
  · rintro ((((h | ⟨j, ⟨h1, h2⟩, h3, h4⟩) | ⟨h3, h4⟩) | ⟨j, ⟨h1, h2⟩, h3, h4⟩) |
      ⟨j, ⟨h1, h2⟩, h3, h4⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨j, ⟨h1, by omega⟩, h3, h4⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h3, h4⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, ⟨h1, by omega⟩, h3, h4⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, ⟨h1, by omega⟩, h3, h4⟩)))
  · rintro (h | ⟨j, ⟨h1, h2⟩, h3, h4⟩ | ⟨h3, h4⟩ | ⟨j, ⟨h1, h2⟩, h3, h4⟩ | ⟨j, ⟨h1, h2⟩, h3, h4⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, ⟨h1, by omega⟩, h3, h4⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨h3, h4⟩))
    · exact Or.inl (Or.inr ⟨j, ⟨h1, by omega⟩, h3, h4⟩)
    · exact Or.inr ⟨j, ⟨h1, by omega⟩, h3, h4⟩

lemma sum_ite_single (S : Finset ℕ) (c : ℕ → ℤ) (b : ℕ → Bool) (s : ℤ) (j0 : ℕ) (hj0 : j0 ∈ S)
    (h0 : s = c j0) (hne : ∀ j ∈ S, j ≠ j0 → s ≠ c j) :
    ∑ j ∈ S, (if s = c j then ((b j).toNat : ℤ) else 0) = ((b j0).toNat : ℤ) := by
  rw [Finset.sum_eq_single j0]
  · simp [h0]
  · intro j hj hne'
    rw [if_neg (hne j hj hne')]
  · intro h; exact absurd hj0 h

lemma sum_ite_single2 (S : Finset ℕ) (c : ℕ → ℤ) (b : ℕ → Bool) (s : ℤ) (j0 : ℕ) (hj0 : j0 ∈ S)
    (h0 : s = c j0 ∨ s = c j0 + 1) (hne : ∀ j ∈ S, j ≠ j0 → s ≠ c j ∧ s ≠ c j + 1) :
    ∑ j ∈ S, ((if s = c j then ((b j).toNat : ℤ) else 0) +
      (if s = c j + 1 then ((b j).toNat : ℤ) else 0)) = ((b j0).toNat : ℤ) := by
  rw [Finset.sum_eq_single j0]
  · rcases h0 with h | h
    · rw [if_pos h, if_neg (by omega)]; simp
    · rw [if_pos h, if_neg (by omega)]; simp
  · intro j hj hne'
    rw [if_neg (hne j hj hne').1, if_neg (hne j hj hne').2]; rfl
  · intro h; exact absurd hj0 h

lemma sum_ite_zero (S : Finset ℕ) (c : ℕ → ℤ) (b : ℕ → Bool) (s : ℤ)
    (h : ∀ j ∈ S, s = c j → b j = false) :
    ∑ j ∈ S, (if s = c j then ((b j).toNat : ℤ) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hs : s = c j
  · rw [if_pos hs, h j hj hs]; rfl
  · rw [if_neg hs]

lemma sum_ite_zero2 (S : Finset ℕ) (c : ℕ → ℤ) (b : ℕ → Bool) (s : ℤ)
    (h : ∀ j ∈ S, (s = c j ∨ s = c j + 1) → b j = false) :
    ∑ j ∈ S, ((if s = c j then ((b j).toNat : ℤ) else 0) +
      (if s = c j + 1 then ((b j).toNat : ℤ) else 0)) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hs : s = c j
  · rw [if_pos hs, if_neg (by omega), h j hj (Or.inl hs)]; rfl
  · by_cases hs' : s = c j + 1
    · rw [if_neg hs, if_pos hs', h j hj (Or.inr hs')]; rfl
    · rw [if_neg hs, if_neg hs']; rfl

lemma bsum_out (m : ℕ) (f : St) (s : ℤ) (h : s < 0 ∨ (p m : ℤ) ≤ s) : bsum m f s = 0 := by
  have hp := p_int m
  unfold bsum sOut sPtr
  rw [sum_ite_zero (c := fun j => (piRow m j : ℤ)) (b := fun j => f.row j) _ _ (by
        intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pR_int] at hs; omega),
      sum_ite_zero2 (c := fun j => (piOut m j : ℤ)) (b := fun j => f.out j) _ _ (by
        intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pO_int] at hs; omega),
      sum_ite_zero2 (c := fun j => (piPtr m j : ℤ)) (b := fun j => f.ptr j) _ _ (by
        intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pP_int] at hs; omega)]
  simp only [pT_int]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp


lemma block_toNat_eq (m : ℕ) (f : St) (s : ℕ) :
    ((block m f s).toNat : ℤ) = bsum m f (s : ℤ) := by
  have hmem : ∀ j, 1 ≤ j → j ≤ m → j ∈ Finset.Icc 1 m := fun j h1 h2 => Finset.mem_Icc.2 ⟨h1, h2⟩
  have hmem' : ∀ j, 1 ≤ j → j ≤ m + 1 → j ∈ Finset.Icc 1 (m + 1) :=
    fun j h1 h2 => Finset.mem_Icc.2 ⟨h1, h2⟩
  by_cases hb : block m f s = true
  · have hb' := hb
    rw [block_true_iff] at hb'
    rw [hb]
    unfold bsum sOut sPtr
    rcases hb' with h0 | ⟨j0, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨hs, hf⟩ | ⟨j0, ⟨hj1, hj2⟩, hs, hf⟩ |
      ⟨j0, ⟨hj1, hj2⟩, hs, hf⟩
    · subst h0
      rw [sum_ite_zero (c := fun j => (piRow m j : ℤ)) (b := fun j => f.row j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pR_int] at hs; omega),
        sum_ite_zero2 (c := fun j => (piOut m j : ℤ)) (b := fun j => f.out j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pO_int] at hs; omega),
        sum_ite_zero2 (c := fun j => (piPtr m j : ℤ)) (b := fun j => f.ptr j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pP_int] at hs; omega)]
      simp only [pT_int, Nat.cast_zero]
      have h1 : (0 : ℤ) ≠ 63 * m + 129 := by omega
      have h2 : (0 : ℤ) ≠ 63 * m + 129 + 1 := by omega
      simp [h1, h2]
    · have hs' : (s : ℤ) = (piRow m j0 : ℤ) := by exact_mod_cast hs
      rw [sum_ite_single (Finset.Icc 1 m) (fun j => (piRow m j : ℤ)) (fun j => f.row j) _ j0
            (hmem _ hj1 hj2) hs' (by
            intro j hj hne hs; simp only [pR_int] at hs hs'; omega),
        sum_ite_zero2 (c := fun j => (piOut m j : ℤ)) (b := fun j => f.out j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pO_int] at hs
            simp only [pR_int] at hs'; omega),
        sum_ite_zero2 (c := fun j => (piPtr m j : ℤ)) (b := fun j => f.ptr j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pP_int] at hs
            simp only [pR_int] at hs'; omega)]
      simp only [pT_int]
      simp only [pR_int] at hs'
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [hf]; simp
    · have hs' : (s : ℤ) = (piTest m : ℤ) ∨ (s : ℤ) = (piTest m : ℤ) + 1 := by
        rcases hs with h | h
        exacts [Or.inl (by exact_mod_cast h), Or.inr (by exact_mod_cast h)]
      rw [sum_ite_zero (c := fun j => (piRow m j : ℤ)) (b := fun j => f.row j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pR_int] at hs
            simp only [pT_int] at hs'; omega),
        sum_ite_zero2 (c := fun j => (piOut m j : ℤ)) (b := fun j => f.out j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pO_int] at hs
            simp only [pT_int] at hs'; omega),
        sum_ite_zero2 (c := fun j => (piPtr m j : ℤ)) (b := fun j => f.ptr j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pP_int] at hs
            simp only [pT_int] at hs'; omega)]
      simp only [pT_int] at hs' ⊢
      rw [if_neg (by omega)]
      rcases hs' with h | h
      · rw [if_pos h, if_neg (by omega), hf]; simp
      · rw [if_neg (by omega), if_pos h, hf]; simp
    · have hs' : (s : ℤ) = (piOut m j0 : ℤ) ∨ (s : ℤ) = (piOut m j0 : ℤ) + 1 := by
        rcases hs with h | h
        exacts [Or.inl (by exact_mod_cast h), Or.inr (by exact_mod_cast h)]
      rw [sum_ite_zero (c := fun j => (piRow m j : ℤ)) (b := fun j => f.row j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pR_int] at hs
            simp only [pO_int] at hs'; omega),
        sum_ite_single2 (Finset.Icc 1 m) (fun j => (piOut m j : ℤ)) (fun j => f.out j) _ j0
            (hmem _ hj1 hj2) hs' (by
            intro j hj hne; simp only [Finset.mem_Icc] at hj; simp only [pO_int]
            simp only [pO_int] at hs'; omega),
        sum_ite_zero2 (c := fun j => (piPtr m j : ℤ)) (b := fun j => f.ptr j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pP_int] at hs
            simp only [pO_int] at hs'; omega)]
      simp only [pT_int]
      simp only [pO_int] at hs'
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [hf]; simp
    · have hs' : (s : ℤ) = (piPtr m j0 : ℤ) ∨ (s : ℤ) = (piPtr m j0 : ℤ) + 1 := by
        rcases hs with h | h
        exacts [Or.inl (by exact_mod_cast h), Or.inr (by exact_mod_cast h)]
      rw [sum_ite_zero (c := fun j => (piRow m j : ℤ)) (b := fun j => f.row j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pR_int] at hs
            simp only [pP_int] at hs'; omega),
        sum_ite_zero2 (c := fun j => (piOut m j : ℤ)) (b := fun j => f.out j) _ _ (by
            intro j hj hs; simp only [Finset.mem_Icc] at hj; simp only [pO_int] at hs
            simp only [pP_int] at hs'; omega),
        sum_ite_single2 (Finset.Icc 1 (m + 1)) (fun j => (piPtr m j : ℤ)) (fun j => f.ptr j) _ j0
            (hmem' _ hj1 hj2) hs' (by
            intro j hj hne; simp only [Finset.mem_Icc] at hj; simp only [pP_int]
            simp only [pP_int] at hs'; omega)]
      simp only [pT_int]
      simp only [pP_int] at hs'
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [hf]; simp
  · rw [Bool.not_eq_true] at hb
    rw [hb]
    have hb' : ¬ block m f s = true := by simp [hb]
    rw [block_true_iff] at hb'
    push Not at hb'
    obtain ⟨h0, hr, ht, ho, hp⟩ := hb'
    unfold bsum sOut sPtr
    rw [sum_ite_zero (c := fun j => (piRow m j : ℤ)) (b := fun j => f.row j) _ _ (by
          intro j hj hs; simp only [Finset.mem_Icc] at hj
          have := hr j ⟨hj.1, hj.2⟩ (by exact_mod_cast hs)
          simpa using this),
      sum_ite_zero2 (c := fun j => (piOut m j : ℤ)) (b := fun j => f.out j) _ _ (by
          intro j hj hs; simp only [Finset.mem_Icc] at hj
          have := ho j ⟨hj.1, hj.2⟩ (by
            rcases hs with h | h
            · left; exact_mod_cast h
            · right; exact_mod_cast h)
          simpa using this),
      sum_ite_zero2 (c := fun j => (piPtr m j : ℤ)) (b := fun j => f.ptr j) _ _ (by
          intro j hj hs; simp only [Finset.mem_Icc] at hj
          have := hp j ⟨hj.1, hj.2⟩ (by
            rcases hs with h | h
            · left; exact_mod_cast h
            · right; exact_mod_cast h)
          simpa using this)]
    have ht' : (s = piTest m ∨ s = piTest m + 1) → f.test = false := by
      intro h; simpa using ht h
    rw [if_neg (by omega)]
    by_cases hA : (s : ℤ) = piTest m
    · rw [if_pos hA, ht' (Or.inl (by exact_mod_cast hA))]
      rw [if_neg (by omega)]; simp
    · by_cases hB : (s : ℤ) = piTest m + 1
      · rw [if_neg hA, if_pos hB, ht' (Or.inr (by exact_mod_cast hB))]; simp
      · rw [if_neg hA, if_neg hB]; simp

end AutoregLTF.Dev.Claim2
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace AutoregLTF.Dev.Claim2
open AutoregLTF AutoregLTF.Dev.Claim1

lemma a_out (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (ℓ : ℤ) (h : ℓ < 1 ∨ (p m : ℤ) + 1 < ℓ) :
    aCoef m θ ℓ = 0 := by
  apply aCoef_zero_of_not_mem
  · intro e he hel
    have := claim1_range m hm θ e he
    omega
  · intro e he hel
    have := upd_range m hm e he
    omega

lemma sum_delta (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (T c v : ℤ) :
    ∑ ℓ ∈ Finset.Icc 1 (p m + 1), aCoef m θ (ℓ : ℤ) * (if T - (ℓ : ℤ) = c then v else 0) =
      aCoef m θ (T - c) * v := by
  by_cases h : 1 ≤ T - c ∧ T - c ≤ (p m : ℤ) + 1
  · rw [Finset.sum_eq_single (T - c).toNat]
    · have : ((T - c).toNat : ℤ) = T - c := by omega
      rw [this]; simp
    · intro ℓ hℓ hne
      rw [if_neg (by omega), mul_zero]
    · intro hn
      exfalso; apply hn
      simp only [Finset.mem_Icc]; omega
  · rw [a_out m hm θ _ (by omega), zero_mul]
    apply Finset.sum_eq_zero
    intro ℓ hℓ
    simp only [Finset.mem_Icc] at hℓ
    rw [if_neg (by omega), mul_zero]

lemma lin_sum (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (S : Finset ℕ) (c v : ℕ → ℤ) (T : ℤ) :
    ∑ ℓ ∈ Finset.Icc 1 (p m + 1), aCoef m θ (ℓ : ℤ) *
      ∑ j ∈ S, (if T - (ℓ : ℤ) = c j then v j else 0) =
    ∑ j ∈ S, aCoef m θ (T - c j) * v j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact sum_delta m hm θ T (c j) (v j)

lemma lin_sum2 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (S : Finset ℕ) (c v : ℕ → ℤ) (T : ℤ) :
    ∑ ℓ ∈ Finset.Icc 1 (p m + 1), aCoef m θ (ℓ : ℤ) *
      ∑ j ∈ S, ((if T - (ℓ : ℤ) = c j then v j else 0) +
        (if T - (ℓ : ℤ) = c j + 1 then v j else 0)) =
    ∑ j ∈ S, (aCoef m θ (T - c j) + aCoef m θ (T - (c j + 1))) * v j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [add_mul, ← sum_delta m hm θ T (c j) (v j), ← sum_delta m hm θ T (c j + 1) (v j),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ℓ _
  ring

/-- the contribution of one block `f` seen from the position `T` -/
def Qs (m : ℕ) (θ : ℕ → ℤ) (T : ℤ) (f : St) : ℤ :=
  aCoef m θ T +
  ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) +
  (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) +
  ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) +
    aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) +
  ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) +
    aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ)

lemma lam_bsum (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (f : St) (T : ℤ) :
    ∑ ℓ ∈ Finset.Icc 1 (p m + 1), aCoef m θ (ℓ : ℤ) * bsum m f (T - (ℓ : ℤ)) =
      Qs m θ T f := by
  unfold bsum Qs
  simp only [mul_add, Finset.sum_add_distrib]
  unfold sOut sPtr
  rw [lin_sum m hm θ (Finset.Icc 1 m) (fun j => (piRow m j : ℤ)) (fun j => ((f.row j).toNat : ℤ)) T,
    lin_sum2 m hm θ (Finset.Icc 1 m) (fun j => (piOut m j : ℤ)) (fun j => ((f.out j).toNat : ℤ)) T,
    lin_sum2 m hm θ (Finset.Icc 1 (m + 1)) (fun j => (piPtr m j : ℤ))
      (fun j => ((f.ptr j).toNat : ℤ)) T]
  have h1 := sum_delta m hm θ T 0 1
  have h2 := sum_delta m hm θ T (piTest m : ℤ) (f.test.toNat : ℤ)
  have h3 := sum_delta m hm θ T ((piTest m : ℤ) + 1) (f.test.toNat : ℤ)
  simp only [sub_zero, mul_one] at h1
  rw [h1, h2, h3]
  ring

lemma Ehat_toNat (m : ℕ) (θ : ℕ → ℤ) (i t : ℕ) (k : ℤ) :
    ((Ehat m θ i t k).toNat : ℤ) =
      bsum m (state m θ i t) (k + p m) + bsum m (state m θ i (t + 1)) k := by
  unfold Ehat E
  by_cases h1 : k < -(p m : ℤ)
  · rw [if_pos h1, bsum_out m _ _ (by omega), bsum_out m _ _ (by omega)]; rfl
  · by_cases h2 : k < 0
    · rw [if_neg h1, if_pos h2, block_toNat_eq, bsum_out m _ k (by omega)]
      have : (((k + p m).toNat : ℕ) : ℤ) = k + p m := by omega
      rw [this]; ring
    · rw [if_neg h1, if_neg h2, block_toNat_eq, bsum_out m _ (k + p m) (by omega)]
      have : ((k.toNat : ℕ) : ℤ) = k := by omega
      rw [this]; ring

lemma sigma_eq (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (i t r : ℕ) :
    sigma m θ i t r = -Bconst m + Qs m θ ((r : ℤ) + p m) (state m θ i t) +
      Qs m θ (r : ℤ) (state m θ i (t + 1)) := by
  unfold sigma
  have : ∀ ℓ ∈ Finset.Icc 1 (p m + 1), aCoef m θ (ℓ : ℤ) * ((Ehat m θ i t ((r : ℤ) - ℓ)).toNat : ℤ) =
      aCoef m θ (ℓ : ℤ) * bsum m (state m θ i t) (((r : ℤ) + p m) - (ℓ : ℤ)) +
      aCoef m θ (ℓ : ℤ) * bsum m (state m θ i (t + 1)) ((r : ℤ) - (ℓ : ℤ)) := by
    intro ℓ _
    rw [Ehat_toNat, ← mul_add]
    congr 2
    · ring_nf
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, lam_bsum m hm, lam_bsum m hm]
  ring

end AutoregLTF.Dev.Claim2
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
namespace AutoregLTF.Dev.Claim2
open AutoregLTF

lemma old_0 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (T : ℤ) (hT : T = 378 * (m + 2)) :
    Qs m θ T f = Bconst m + 1 := by
  have eA : aCoef m θ T = Bconst m + 1 := a_p0 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma new_0 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (T : ℤ) (hT : T = 0) :
    Qs m θ T f = 0 := by
  have eA : aCoef m θ T = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma old_row (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m) (T : ℤ) (hT : T = 63 * m + 132 + 63 * k + 378 * (m + 2)) :
    Qs m θ T f = (Bconst m + 1) * ((f.row k).toNat : ℤ) := by
  have eA : aCoef m θ T = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = (Bconst m + 1) * ((f.row k).toNat : ℤ) := by
    rw [Finset.sum_eq_single k (fun j hj hne => by
        simp only [Finset.mem_Icc] at hj
        have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
        rw [z, zero_mul]) (fun hn => absurd (Finset.mem_Icc.2 ⟨hk.1, by omega⟩) hn)]
    have v : aCoef m θ (T - (piRow m k : ℤ)) = Bconst m + 1 := a_p0 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma new_row (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m) (T : ℤ) (hT : T = 63 * m + 132 + 63 * k) :
    Qs m θ T f = 0 := by
  have eA : aCoef m θ T = 0 := a_zM m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma old_test (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (T : ℤ) (hT : T = (63 * m + 129) + 378 * (m + 2)) :
    Qs m θ T f = (∑ j ∈ Finset.Icc 1 m, (4 * θ j) * ((f.row j).toNat : ℤ)) + 2 * (f.test.toNat : ℤ) + (∑ j ∈ Finset.Icc 1 m, (-(2 ^ (j + 1))) * ((f.out j).toNat : ℤ)) + ∑ j ∈ Finset.Icc 1 m, (-(2 ^ (j + 1))) * ((f.ptr j).toNat : ℤ) := by
  have eA : aCoef m θ T = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = ∑ j ∈ Finset.Icc 1 m, (4 * θ j) * ((f.row j).toNat : ℤ) := by
    apply Finset.sum_congr rfl
    intro j hj
    have h := Finset.mem_Icc.1 hj
    have v : aCoef m θ (T - (piRow m j : ℤ)) = 4 * θ j := a17a m hm θ hθ _ j h (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 2 * (f.test.toNat : ℤ) := by
    have v1 : aCoef m θ (T - (piTest m : ℤ)) = Bconst m + 1 := a_p0 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have v2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 1 - Bconst m := a_pm1 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v1, v2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = ∑ j ∈ Finset.Icc 1 m, (-(2 ^ (j + 1))) * ((f.out j).toNat : ℤ) := by
    apply Finset.sum_congr rfl
    intro j hj
    have h := Finset.mem_Icc.1 hj
    have v1 : aCoef m θ (T - (piOut m j : ℤ)) = -(2 ^ (j + 1)) := a17b m hm θ hθ _ j h (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have v2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v1, v2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = ∑ j ∈ Finset.Icc 1 m, (-(2 ^ (j + 1))) * ((f.ptr j).toNat : ℤ) := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have z1 : aCoef m θ (T - (piPtr m (m + 1) : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piPtr m (m + 1) : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2, zero_add, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have h := Finset.mem_Icc.1 hj
    have v1 : aCoef m θ (T - (piPtr m j : ℤ)) = -(2 ^ (j + 1)) := a17c m hm θ hθ _ j h (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have v2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [v1, v2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma new_test (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (T : ℤ) (hT : T = (63 * m + 129)) :
    Qs m θ T f = Bconst m + 1 := by
  have eA : aCoef m θ T = Bconst m + 1 := a_T0 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma old_test1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (T : ℤ) (hT : T = 63 * m + 130 + 378 * (m + 2)) :
    Qs m θ T f = 0 := by
  have eA : aCoef m θ T = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := by exact a_zero2 m θ _ (-(j : ℤ) + 6 * (m : ℤ) + 11) 61 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); constructor <;> intro hq' <;> omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have v1 : aCoef m θ (T - (piTest m : ℤ)) = -Bconst m - 1 := a_pp1 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have v2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = Bconst m + 1 := a_p0 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v1, v2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h := Finset.mem_Icc.1 hj
    have v1 : aCoef m θ (T - (piOut m j : ℤ)) = 2 ^ (j + 1) := a18b m hm θ hθ _ j h (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have v2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = -(2 ^ (j + 1)) := a17b m hm θ hθ _ j h (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v1, v2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h := Finset.mem_Icc.1 hj
    by_cases hjm : j ≤ m
    · have v1 : aCoef m θ (T - (piPtr m j : ℤ)) = 2 ^ (j + 1) := a18c m hm θ hθ _ j ⟨h.1, hjm⟩ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
      have v2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = -(2 ^ (j + 1)) := a17c m hm θ hθ _ j ⟨h.1, hjm⟩ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
      rw [v1, v2]; ring
    · have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
      have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
      rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma new_test1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (T : ℤ) (hT : T = 63 * m + 130) :
    Qs m θ T f = (Bconst m - 1) + 2 * (f.test.toNat : ℤ) := by
  have eA : aCoef m θ T = Bconst m - 1 := a_T1 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 2 * (f.test.toNat : ℤ) := by
    have v1 : aCoef m θ (T - (piTest m : ℤ)) = 2 := a_one m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

set_option maxHeartbeats 1600000 in
lemma old_out (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m) (T : ℤ) (hT : T = 63 * m + 141 + 63 * k + 378 * (m + 2)) :
    Qs m θ T f = 2 * ((f.out k).toNat : ℤ) + ((f.ptr k).toNat : ℤ) := by
  have eA : aCoef m θ T = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 2 * ((f.out k).toNat : ℤ) := by
    rw [Finset.sum_eq_single k (fun j hj hne => by
        simp only [Finset.mem_Icc] at hj
        have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
        have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
        rw [z1, z2]; ring) (fun hn => absurd (Finset.mem_Icc.2 hk) hn)]
    have v1 : aCoef m θ (T - (piOut m k : ℤ)) = Bconst m + 1 := a_p0 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have v2 : aCoef m θ (T - ((piOut m k : ℤ) + 1)) = 1 - Bconst m := a_pm1 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v1, v2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = ((f.ptr k).toNat : ℤ) := by
    rw [Finset.sum_eq_single k (fun j hj hne => by
        simp only [Finset.mem_Icc] at hj
        have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 33 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 33 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 27 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 27 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
        have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 32 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 32 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 26 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 26 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
        rw [z1, z2]; ring) (fun hn => absurd (Finset.mem_Icc.2 ⟨hk.1, by omega⟩) hn)]
    have v1 : aCoef m θ (T - (piPtr m k : ℤ)) = 1 := a17e m hm θ hθ _ k hk (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piPtr m k : ℤ) + 1)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hq | hq <;> (try simp only [hq] at hT)) <;> [exact a_zero2 m θ _ (6 * (m : ℤ) + 11) 32 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (6 * (m : ℤ) + 11) 26 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); constructor <;> intro hq' <;> omega)]
    rw [v1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma new_out (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m) (T : ℤ) (hT : T = 63 * m + 141 + 63 * k) :
    Qs m θ T f = (Bconst m - 2) + (f.test.toNat : ℤ) := by
  have eA : aCoef m θ T = Bconst m - 2 := a_O0 m hm θ hθ _ k hk (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = (f.test.toNat : ℤ) := by
    have v1 : aCoef m θ (T - (piTest m : ℤ)) = 1 := a17d m hm θ hθ _ k hk (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

set_option maxHeartbeats 1600000 in
lemma old_out1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m) (T : ℤ) (hT : T = 63 * m + 142 + 63 * k + 378 * (m + 2)) :
    Qs m θ T f = 0 := by
  have eA : aCoef m θ T = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h := Finset.mem_Icc.1 hj
    by_cases hjk : j = k
    · subst hjk
      have v1 : aCoef m θ (T - (piOut m j : ℤ)) = -Bconst m - 1 := a_pp1 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
      have v2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = Bconst m + 1 := a_p0 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
      rw [v1, v2]; ring
    · have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
      have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
      rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h := Finset.mem_Icc.1 hj
    by_cases hjk : j = k
    · subst hjk
      have v1 : aCoef m θ (T - (piPtr m j : ℤ)) = -1 := a18e m hm θ hθ _ j hk (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
      have v2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 1 := a17e m hm θ hθ _ j hk (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
      rw [v1, v2]; ring
    · have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 34 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 34 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 28 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 28 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
      have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 33 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 33 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 27 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 27 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
      rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma new_out1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m) (T : ℤ) (hT : T = 63 * m + 142 + 63 * k) :
    Qs m θ T f = (Bconst m - 1) + 2 * ((f.out k).toNat : ℤ) := by
  have eA : aCoef m θ T = Bconst m - 1 := a_O1 m hm θ hθ _ k hk (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have v1 : aCoef m θ (T - (piTest m : ℤ)) = -1 := a18d m hm θ hθ _ k hk (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have v2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 1 := a17d m hm θ hθ _ k hk (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v1, v2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 2 * ((f.out k).toNat : ℤ) := by
    rw [Finset.sum_eq_single k (fun j hj hne => by
        simp only [Finset.mem_Icc] at hj
        have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
        have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
        rw [z1, z2]; ring) (fun hn => absurd (Finset.mem_Icc.2 hk) hn)]
    have v1 : aCoef m θ (T - (piOut m k : ℤ)) = 2 := a_one m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have v2 : aCoef m θ (T - ((piOut m k : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [v1, v2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

set_option maxHeartbeats 1600000 in
lemma old_ptr (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m + 1) (T : ℤ) (hT : T = 63 * m + 171 + 63 * k + 6 * ((k : ℤ) % 2) + 378 * (m + 2)) :
    Qs m θ T f = 2 * ((f.ptr k).toNat : ℤ) + (if k ≤ m then 4 * ((f.ptr (k + 1)).toNat : ℤ) else 0) := by
  have eA : aCoef m θ T = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 2 * ((f.ptr k).toNat : ℤ) + (if k ≤ m then 4 * ((f.ptr (k + 1)).toNat : ℤ) else 0) := by
    have v1 : aCoef m θ (T - (piPtr m k : ℤ)) = Bconst m + 1 := by rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hq | hq <;> (try simp only [hq] at hT) <;> exact (a_p0 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have v2 : aCoef m θ (T - ((piPtr m k : ℤ) + 1)) = 1 - Bconst m := by rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hq | hq <;> (try simp only [hq] at hT) <;> exact (a_pm1 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    by_cases hkm : k ≤ m
    · rw [Finset.sum_eq_add k (k + 1) (by omega) (fun j hj hne => by
          simp only [Finset.mem_Icc] at hj
          have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 0 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 6 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 57 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 0 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
          have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 62 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 5 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 56 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 62 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
          rw [z1, z2]; ring) (fun hn => absurd (Finset.mem_Icc.2 hk) hn)
        (fun hn => absurd (Finset.mem_Icc.2 ⟨by omega, by omega⟩) hn)]
      have v3 : aCoef m θ (T - (piPtr m (k + 1) : ℤ)) = 4 :=
        a17f m hm θ hθ _ k ⟨hk.1, hkm⟩ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
      have z4 : aCoef m θ (T - ((piPtr m (k + 1) : ℤ) + 1)) = 0 := by (rcases Int.emod_two_eq_zero_or_one ((k + 1 : ℕ) : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (6 * (m : ℤ) + 10) 62 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (6 * (m : ℤ) + 11) 5 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (6 * (m : ℤ) + 10) 56 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (6 * (m : ℤ) + 10) 62 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
      rw [v1, v2, v3, z4, if_pos hkm]; ring
    · have hk' : k = m + 1 := by omega
      rw [Finset.sum_eq_single k (fun j hj hne => by
          simp only [Finset.mem_Icc] at hj
          have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 0 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 6 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 57 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 0 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
          have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 62 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 5 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 56 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 62 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
          rw [z1, z2]; ring) (fun hn => absurd (Finset.mem_Icc.2 hk) hn)]
      rw [v1, v2, if_neg hkm]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma new_ptr (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m + 1) (T : ℤ) (hT : T = 63 * m + 171 + 63 * k + 6 * ((k : ℤ) % 2)) :
    Qs m θ T f = Bconst m - 3 := by
  have eA : aCoef m θ T = Bconst m - 3 := a_P0 m hm θ hθ _ k hk (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT) <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT) <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

set_option maxHeartbeats 1600000 in
lemma old_ptr1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m + 1) (T : ℤ) (hT : T = 63 * m + 172 + 63 * k + 6 * ((k : ℤ) % 2) + 378 * (m + 2)) :
    Qs m θ T f = 0 := by
  have eA : aCoef m θ T = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zL m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h := Finset.mem_Icc.1 hj
    by_cases hjk : j = k
    · subst hjk
      have v1 : aCoef m θ (T - (piPtr m j : ℤ)) = -Bconst m - 1 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> (try simp only [hq] at hT) <;> exact (a_pp1 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
      have v2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = Bconst m + 1 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> (try simp only [hq] at hT) <;> exact (a_p0 m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
      rw [v1, v2]; ring
    · by_cases hjk' : j = k + 1 ∧ k ≤ m
      · obtain ⟨rfl, hkm⟩ := hjk'
        have v1 : aCoef m θ (T - (piPtr m (k + 1) : ℤ)) = -4 :=
          a18f m hm θ hθ _ k ⟨hk.1, hkm⟩ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
        have v2 : aCoef m θ (T - ((piPtr m (k + 1) : ℤ) + 1)) = 4 :=
          a17f m hm θ hθ _ k ⟨hk.1, hkm⟩ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
        rw [v1, v2]; ring
      · have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 1 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 7 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 58 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 1 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
        have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by (rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT)) <;> [exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 0 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 6 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 11) 57 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega); exact a_zero2 m θ _ (-(j : ℤ) + (k : ℤ) + 6 * (m : ℤ) + 12) 0 (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (by norm_num) (by norm_num) (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); omega) (fun j' h1' h2' => by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq, hk2]); constructor <;> intro hq' <;> omega)]
        rw [z1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

lemma new_ptr1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m + 1) (T : ℤ) (hT : T = 63 * m + 172 + 63 * k + 6 * ((k : ℤ) % 2)) :
    Qs m θ T f = (Bconst m - 1) + 2 * ((f.ptr k).toNat : ℤ) := by
  have eA : aCoef m θ T = Bconst m - 1 := a_P1 m hm θ hθ _ k hk (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
  have eR : ∑ j ∈ Finset.Icc 1 m, aCoef m θ (T - (piRow m j : ℤ)) * ((f.row j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z : aCoef m θ (T - (piRow m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z, zero_mul]
  have eT : (aCoef m θ (T - (piTest m : ℤ)) + aCoef m θ (T - ((piTest m : ℤ) + 1))) * (f.test.toNat : ℤ) = 0 := by
    have z1 : aCoef m θ (T - (piTest m : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piTest m : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eO : ∑ j ∈ Finset.Icc 1 m, (aCoef m θ (T - (piOut m j : ℤ)) + aCoef m θ (T - ((piOut m j : ℤ) + 1))) * ((f.out j).toNat : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have z1 : aCoef m θ (T - (piOut m j : ℤ)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    have z2 : aCoef m θ (T - ((piOut m j : ℤ) + 1)) = 0 := a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int]); omega)
    rw [z1, z2]; ring
  have eP : ∑ j ∈ Finset.Icc 1 (m + 1), (aCoef m θ (T - (piPtr m j : ℤ)) + aCoef m θ (T - ((piPtr m j : ℤ) + 1))) * ((f.ptr j).toNat : ℤ) = 2 * ((f.ptr k).toNat : ℤ) := by
    rw [Finset.sum_eq_single k (fun j hj hne => by
        simp only [Finset.mem_Icc] at hj
        have z1 : aCoef m θ (T - (piPtr m j : ℤ)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT) <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
        have z2 : aCoef m θ (T - ((piPtr m j : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (j : ℤ) with hq | hq <;> rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hk2 | hk2 <;> (try simp only [hk2] at hT) <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
        rw [z1, z2]; ring) (fun hn => absurd (Finset.mem_Icc.2 hk) hn)]
    have v1 : aCoef m θ (T - (piPtr m k : ℤ)) = 2 := by rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hq | hq <;> (try simp only [hq] at hT) <;> exact (a_one m hm θ hθ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    have z2 : aCoef m θ (T - ((piPtr m k : ℤ) + 1)) = 0 := by rcases Int.emod_two_eq_zero_or_one (k : ℤ) with hq | hq <;> (try simp only [hq] at hT) <;> exact (a_zS m hm θ _ (by (try simp only [p_int, pT_int, pR_int, pO_int, pP_int, hq]); omega))
    rw [v1, z2]; ring
  unfold Qs
  rw [eA, eR, eT, eO, eP]
  ring

end AutoregLTF.Dev.Claim2
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace AutoregLTF.Dev.Claim2
open AutoregLTF

lemma blk_zero (m : ℕ) (f : St) : block m f 0 = true := by
  simp [block]

lemma blk_row (m : ℕ) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m) :
    block m f (piRow m k) = f.row k := by
  rw [Bool.eq_iff_iff, block_true_iff]
  constructor
  · rintro (h | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩)
    · simp only [piRow, p] at h; omega
    · have : j = k := by simp only [piRow, p] at hs; omega
      subst this; exact hf
    · simp only [piRow, piTest, p] at hs; omega
    · simp only [piRow, piOut, p] at hs; omega
    · simp only [piRow, piPtr, p] at hs; omega
  · intro h; exact Or.inr (Or.inl ⟨k, hk, rfl, h⟩)

lemma blk_test0 (m : ℕ) (f : St) : block m f (piTest m) = f.test := by
  rw [Bool.eq_iff_iff, block_true_iff]
  constructor
  · rintro (h | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩)
    · simp only [piTest, p] at h; omega
    · simp only [piRow, piTest, p] at hs; omega
    · exact hf
    · simp only [piOut, piTest, p] at hs; omega
    · simp only [piPtr, piTest, p] at hs; omega
  · intro h; exact Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, h⟩))

lemma blk_test1 (m : ℕ) (f : St) : block m f (piTest m + 1) = f.test := by
  rw [Bool.eq_iff_iff, block_true_iff]
  constructor
  · rintro (h | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩)
    · simp only [piTest, p] at h; omega
    · simp only [piRow, piTest, p] at hs; omega
    · exact hf
    · simp only [piOut, piTest, p] at hs; omega
    · simp only [piPtr, piTest, p] at hs; omega
  · intro h; exact Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, h⟩))

lemma blk_out0 (m : ℕ) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m) :
    block m f (piOut m k) = f.out k := by
  rw [Bool.eq_iff_iff, block_true_iff]
  constructor
  · rintro (h | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩)
    · simp only [piOut, p] at h; omega
    · simp only [piRow, piOut, p] at hs; omega
    · rcases hs with hs | hs <;> simp only [piOut, piTest, p] at hs <;> omega
    · have : j = k := by rcases hs with hs | hs <;> simp only [piOut, p] at hs <;> omega
      subst this; exact hf
    · rcases hs with hs | hs <;> simp only [piOut, piPtr, p] at hs <;>
        (rcases Nat.mod_two_eq_zero_or_one j with hq | hq <;> omega)
  · intro h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, Or.inl rfl, h⟩)))

lemma blk_out1 (m : ℕ) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m) :
    block m f (piOut m k + 1) = f.out k := by
  rw [Bool.eq_iff_iff, block_true_iff]
  constructor
  · rintro (h | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩)
    · simp only [piOut, p] at h; omega
    · simp only [piRow, piOut, p] at hs; omega
    · rcases hs with hs | hs <;> simp only [piOut, piTest, p] at hs <;> omega
    · have : j = k := by rcases hs with hs | hs <;> simp only [piOut, p] at hs <;> omega
      subst this; exact hf
    · rcases hs with hs | hs <;> simp only [piOut, piPtr, p] at hs <;>
        (rcases Nat.mod_two_eq_zero_or_one j with hq | hq <;> omega)
  · intro h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, Or.inr rfl, h⟩)))

lemma blk_ptr0 (m : ℕ) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m + 1) :
    block m f (piPtr m k) = f.ptr k := by
  rw [Bool.eq_iff_iff, block_true_iff]
  constructor
  · rintro (h | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩)
    · simp only [piPtr, p] at h; omega
    · simp only [piRow, piPtr, p] at hs
      rcases Nat.mod_two_eq_zero_or_one k with hq | hq <;> omega
    · rcases hs with hs | hs <;> simp only [piPtr, piTest, p] at hs <;>
        (rcases Nat.mod_two_eq_zero_or_one k with hq | hq <;> omega)
    · simp only [piOut, piPtr, p] at hs
      rcases hs with hs | hs <;>
        (rcases Nat.mod_two_eq_zero_or_one k with hq | hq <;> omega)
    · have : j = k := by
        rcases hs with hs | hs <;> simp only [piPtr, p] at hs <;>
          (rcases Nat.mod_two_eq_zero_or_one k with hq | hq <;>
           rcases Nat.mod_two_eq_zero_or_one j with hq' | hq' <;> omega)
      subst this; exact hf
  · intro h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, hk, Or.inl rfl, h⟩)))

lemma blk_ptr1 (m : ℕ) (f : St) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m + 1) :
    block m f (piPtr m k + 1) = f.ptr k := by
  rw [Bool.eq_iff_iff, block_true_iff]
  constructor
  · rintro (h | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩ | ⟨j, ⟨hj1, hj2⟩, hs, hf⟩)
    · simp only [piPtr, p] at h; omega
    · simp only [piRow, piPtr, p] at hs
      rcases Nat.mod_two_eq_zero_or_one k with hq | hq <;> omega
    · rcases hs with hs | hs <;> simp only [piPtr, piTest, p] at hs <;>
        (rcases Nat.mod_two_eq_zero_or_one k with hq | hq <;> omega)
    · simp only [piOut, piPtr, p] at hs
      rcases hs with hs | hs <;>
        (rcases Nat.mod_two_eq_zero_or_one k with hq | hq <;> omega)
    · have : j = k := by
        rcases hs with hs | hs <;> simp only [piPtr, p] at hs <;>
          (rcases Nat.mod_two_eq_zero_or_one k with hq | hq <;>
           rcases Nat.mod_two_eq_zero_or_one j with hq' | hq' <;> omega)
      subst this; exact hf
  · intro h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, hk, Or.inr rfl, h⟩)))

lemma Ehat_nat (m : ℕ) (θ : ℕ → ℤ) (i t r : ℕ) :
    Ehat m θ i t (r : ℤ) = block m (state m θ i (t + 1)) r := by
  unfold Ehat E
  rw [if_neg (by omega), if_neg (by omega)]
  simp

lemma dec_of (b : Bool) (s : ℤ) (h1 : b = true → 0 ≤ s) (h2 : b = false → s < 0) :
    b = decide (0 ≤ s) := by
  cases b
  · simp [h2 rfl]
  · simp [h1 rfl]

lemma B_pos (m : ℕ) : 0 < Bconst m := by
  unfold Bconst; positivity

lemma pow_two_succ (j : ℕ) (hj : 1 ≤ j) : (2 : ℤ) ^ (j + 1) = 4 * 2 ^ (j - 1) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp [pow_succ]; ring

lemma test_sum (m : ℕ) (θ : ℕ → ℤ) (f : St) :
    (∑ j ∈ Finset.Icc 1 m, (4 * θ j) * ((f.row j).toNat : ℤ)) +
      (∑ j ∈ Finset.Icc 1 m, (-(2 ^ (j + 1))) * ((f.out j).toNat : ℤ)) +
      (∑ j ∈ Finset.Icc 1 m, (-(2 ^ (j + 1))) * ((f.ptr j).toNat : ℤ)) =
    4 * (∑ j ∈ Finset.Icc 1 m, θ j * ((f.row j).toNat : ℤ) -
      ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * (((f.out j).toNat : ℤ) + ((f.ptr j).toNat : ℤ))) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have := pow_two_succ j (Finset.mem_Icc.1 hj).1
  rw [this]; ring

end AutoregLTF.Dev.Claim2

namespace AutoregLTF
open AutoregLTF.Dev.Claim2 in
theorem chk_claim_2 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (t r : ℕ) (hr : InPi m r) :
    Ehat m θ i t r = decide (0 ≤ sigma m θ i t r) := by
  have hB := B_pos m
  rw [Ehat_nat, sigma_eq m hm]
  have hg : state m θ i (t + 1) = step m θ (state m θ i t) := rfl
  generalize state m θ i t = f at hg ⊢
  generalize state m θ i (t + 1) = g at hg ⊢
  subst hg
  rcases hr with h0 | ⟨k, hk, rfl⟩ | (rfl | rfl) | ⟨k, hk, rfl | rfl⟩ | ⟨k, hk, rfl | rfl⟩
  · subst h0
    rw [old_0 m hm θ hθ f _ (by simp only [p_int] <;> omega), new_0 m hm θ hθ _ _ (by omega),
      blk_zero]
    simp
  · have hk' := Finset.mem_Icc.1 hk
    rw [old_row m hm θ hθ f k hk' _ (by simp only [pR_int, p_int] <;> omega),
      new_row m hm θ hθ _ k hk' _ (by simp only [pR_int] <;> omega), blk_row m _ k hk']
    apply dec_of
    · intro h
      have h' : f.row k = true := h
      simp [h'] <;> omega
    · intro h
      have h' : f.row k = false := h
      simp [h'] <;> omega
  · rw [old_test m hm θ hθ f _ (by simp only [pT_int, p_int] <;> omega),
      new_test m hm θ hθ _ _ (by simp only [pT_int] <;> omega), blk_test0]
    have hts := test_sum m θ f
    have ht1 := Bool.toNat_le f.test
    have ht0 : 0 ≤ ((f.test.toNat : ℕ) : ℤ) := by positivity
    apply dec_of
    · intro h
      have h' : decide (0 ≤ ∑ j ∈ Finset.Icc 1 m, θ j * ((f.row j).toNat : ℤ) -
          ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * (((f.out j).toNat : ℤ) + ((f.ptr j).toNat : ℤ))) =
          true := h
      have h'' := of_decide_eq_true h'
      omega
    · intro h
      have h' : decide (0 ≤ ∑ j ∈ Finset.Icc 1 m, θ j * ((f.row j).toNat : ℤ) -
          ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * (((f.out j).toNat : ℤ) + ((f.ptr j).toNat : ℤ))) =
          false := h
      have h'' := of_decide_eq_false h'
      omega
  · simp only [Nat.cast_add, Nat.cast_one]
    rw [old_test1 m hm θ hθ f _ (by simp only [pT_int, p_int] <;> omega),
      new_test1 m hm θ hθ _ _ (by simp only [pT_int] <;> omega), blk_test1]
    apply dec_of
    · intro h; rw [h]; simp <;> omega
    · intro h; rw [h]; simp <;> omega
  · have hk' := Finset.mem_Icc.1 hk
    rw [old_out m hm θ hθ f k hk' _ (by simp only [pO_int, p_int] <;> omega),
      new_out m hm θ hθ _ k hk' _ (by simp only [pO_int] <;> omega), blk_out0 m _ k hk']
    show decide (2 ≤ 2 * (f.out k).toNat + (f.ptr k).toNat + (step m θ f).test.toNat) = _
    rw [decide_eq_decide]
    omega
  · have hk' := Finset.mem_Icc.1 hk
    simp only [Nat.cast_add, Nat.cast_one]
    rw [old_out1 m hm θ hθ f k hk' _ (by simp only [pO_int, p_int] <;> omega),
      new_out1 m hm θ hθ _ k hk' _ (by simp only [pO_int] <;> omega), blk_out1 m _ k hk']
    apply dec_of
    · intro h; rw [h]; simp <;> omega
    · intro h; rw [h]; simp <;> omega
  · have hk' : 1 ≤ k ∧ k ≤ m + 1 := ⟨(Finset.mem_Icc.1 hk).1, by
      have := (Finset.mem_Icc.1 hk).2; omega⟩
    rw [old_ptr m hm θ hθ f k hk' _ (by simp only [pP_int, p_int] <;> omega),
      new_ptr m hm θ hθ _ k hk' _ (by simp only [pP_int] <;> omega), blk_ptr0 m _ k hk']
    have e : (step m θ f).ptr k = if k ≤ m then f.ptr (k + 1) else false := rfl
    have hu := Bool.toNat_le (f.ptr k)
    rw [e]
    by_cases hkm : k ≤ m
    · rw [if_pos hkm, if_pos hkm]
      apply dec_of
      · intro h; rw [h]; simp <;> omega
      · intro h; rw [h]; simp <;> omega
    · rw [if_neg hkm, if_neg hkm]
      apply dec_of
      · intro h; exact absurd h (by simp)
      · intro _; simp; omega
  · have hk' : 1 ≤ k ∧ k ≤ m + 1 := ⟨(Finset.mem_Icc.1 hk).1, by
      have := (Finset.mem_Icc.1 hk).2; omega⟩
    simp only [Nat.cast_add, Nat.cast_one]
    rw [old_ptr1 m hm θ hθ f k hk' _ (by simp only [pP_int, p_int] <;> omega),
      new_ptr1 m hm θ hθ _ k hk' _ (by simp only [pP_int] <;> omega), blk_ptr1 m _ k hk']
    apply dec_of
    · intro h; rw [h]; simp <;> omega
    · intro h; rw [h]; simp <;> omega

end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_claim_2 := @AutoregLTF.chk_claim_2
