-- Prove2me | solution 1 for AutoregLTF.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:59.617214+00:00
-- url     : https://prove2.me/submissions/d4dec6f3-dcb1-485d-9968-b79ffd9d6d8f

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


end AutoregLTF.Dev.Claim1

namespace AutoregLTF
open AutoregLTF.Dev.Claim1

end AutoregLTF
end

section
set_option autoImplicit false
namespace AutoregLTF
open AutoregLTF.Dev.Claim1

theorem chk_claim_1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) :
    ∀ e ∈ assign0 m θ, (1 ≤ e.1 ∧ e.1 ≤ (p m : ℤ) + 1) ∧
      ∀ e' ∈ assign0 m θ, e'.1 = e.1 → e'.2 = e.2 :=
  fun e he => ⟨claim1_range m hm θ e he, fun e' he' h => claim1_cons m θ e e' he he' h⟩

end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_claim_1 := @AutoregLTF.chk_claim_1
