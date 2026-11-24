-- Prove2me | solution 1 for DerandLDT.lemma_3_18
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T08:09:38.980787+00:00
-- url     : https://prove2.me/submissions/d97a16c5-22a2-43ca-80ca-15cf1662854e

import Mathlib

set_option autoImplicit false

universe u
namespace DerandLDT

namespace A4

/-- Number of edges of `E` inside `U × V`, as a real number. -/
noncomputable def F {α β : Type u} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (U : Finset α) (V : Finset β) : ℝ :=
  ∑ x ∈ U, ∑ y ∈ V, if (x, y) ∈ E then (1:ℝ) else 0

lemma F_erase_left {α β : Type u} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (U : Finset α) (V : Finset β) (x : α) (hx : x ∈ U) :
    F E U V = F E (U.erase x) V + ((V.filter fun y => (x, y) ∈ E).card : ℝ) := by
  unfold F
  rw [← Finset.sum_erase_add U _ hx, Finset.sum_boole]

lemma F_erase_right {α β : Type u} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (U : Finset α) (V : Finset β) (y : β) (hy : y ∈ V) :
    F E U V = F E U (V.erase y) + ((U.filter fun x => (x, y) ∈ E).card : ℝ) := by
  unfold F
  rw [← Finset.sum_boole, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_erase_add V _ hy]

lemma F_left {α β : Type u} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (U : Finset α) (V : Finset β) :
    F E U V = ∑ x ∈ U, ((V.filter fun y => (x, y) ∈ E).card : ℝ) := by
  unfold F
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_boole]

lemma F_right {α β : Type u} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (U : Finset α) (V : Finset β) :
    F E U V = ∑ y ∈ V, ((U.filter fun x => (x, y) ∈ E).card : ℝ) := by
  unfold F
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_boole]

lemma F_full {α β : Type u} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (U : Finset α) (V : Finset β) (hE : E ⊆ U ×ˢ V) :
    F E U V = (E.card : ℝ) := by
  unfold F
  rw [← Finset.sum_product (s := U) (t := V) (f := fun p => if p ∈ E then (1:ℝ) else 0)]
  rw [Finset.sum_boole]
  congr 2
  ext p
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hE h, h⟩

lemma prune {α β : Type u} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (a b : ℝ) (n : ℕ) :
    ∀ (U : Finset α) (V : Finset β), U.card + V.card = n →
    ∃ U' ⊆ U, ∃ V' ⊆ V,
      (∀ x ∈ U', a ≤ ((V'.filter fun y => (x, y) ∈ E).card : ℝ)) ∧
      (∀ y ∈ V', b ≤ ((U'.filter fun x => (x, y) ∈ E).card : ℝ)) ∧
      F E U V - a * U.card - b * V.card ≤ F E U' V' - a * U'.card - b * V'.card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U V hn
  by_cases hU : ∃ x ∈ U, ((V.filter fun y => (x, y) ∈ E).card : ℝ) < a
  · obtain ⟨x, hx, hlt⟩ := hU
    have hpos := Finset.card_pos.mpr ⟨x, hx⟩
    have hc : (U.erase x).card + V.card < n := by
      rw [Finset.card_erase_of_mem hx]; omega
    obtain ⟨U', hU', V', hV', h1, h2, h3⟩ := ih _ hc (U.erase x) V rfl
    refine ⟨U', hU'.trans (Finset.erase_subset _ _), V', hV', h1, h2, ?_⟩
    have e := F_erase_left E U V x hx
    have hcard : ((U.erase x).card : ℝ) = U.card - 1 := by
      rw [Finset.card_erase_of_mem hx, Nat.cast_sub hpos]; simp
    rw [hcard] at h3
    linarith
  by_cases hV : ∃ y ∈ V, ((U.filter fun x => (x, y) ∈ E).card : ℝ) < b
  · obtain ⟨y, hy, hlt⟩ := hV
    have hpos := Finset.card_pos.mpr ⟨y, hy⟩
    have hc : U.card + (V.erase y).card < n := by
      rw [Finset.card_erase_of_mem hy]; omega
    obtain ⟨U', hU', V', hV', h1, h2, h3⟩ := ih _ hc U (V.erase y) rfl
    refine ⟨U', hU', V', hV'.trans (Finset.erase_subset _ _), h1, h2, ?_⟩
    have e := F_erase_right E U V y hy
    have hcard : ((V.erase y).card : ℝ) = V.card - 1 := by
      rw [Finset.card_erase_of_mem hy, Nat.cast_sub hpos]; simp
    rw [hcard] at h3
    linarith
  push Not at hU hV
  exact ⟨U, subset_rfl, V, subset_rfl, hU, hV, le_rfl⟩

end A4

theorem lemma_3_18_main {α β : Type u} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) (E : Finset (α × β)) (hE : E ⊆ U ×ˢ V)
    (ℓ r : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r)
    (hdegU : ∀ u ∈ U, ((E.filter fun e => e.1 = u).card : ℝ) ≤ ℓ)
    (hdegV : ∀ v ∈ V, ((E.filter fun e => e.2 = v).card : ℝ) ≤ r)
    (ε δ : ℝ) (hε : (E.card : ℝ) = ε * ℓ * U.card) (hδ : (E.card : ℝ) = δ * r * V.card) :
    ∃ U' ⊆ U, ∃ V' ⊆ V,
      4 * ε / 5 * (U.card : ℝ) ≤ U'.card ∧ 4 * δ / 5 * (V.card : ℝ) ≤ V'.card ∧
      (∀ u ∈ U', ε * ℓ / 10 ≤ ((V'.filter fun v => (u, v) ∈ E).card : ℝ)) ∧
      (∀ v ∈ V', δ * r / 10 ≤ ((U'.filter fun u => (u, v) ∈ E).card : ℝ)) := by
  rcases E.eq_empty_or_nonempty with hE0 | hEne
  · subst hE0
    simp only [Finset.card_empty, Nat.cast_zero] at hε hδ
    have h1 : ε * U.card = 0 := by
      have : ℓ * (ε * U.card) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    have h2 : δ * V.card = 0 := by
      have : r * (δ * V.card) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    refine ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, ?_, ?_, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]; linarith
    · simp only [Finset.card_empty, Nat.cast_zero]; linarith
    · intro u hu; simp at hu
    · intro v hv; simp at hv
  have hEpos : (0:ℝ) < E.card := by exact_mod_cast hEne.card_pos
  have hUnn : (0:ℝ) ≤ U.card := Nat.cast_nonneg _
  have hVnn : (0:ℝ) ≤ V.card := Nat.cast_nonneg _
  have ha : 0 < ε * ℓ := by
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hUnn
    linarith
  have hb : 0 < δ * r := by
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hVnn
    linarith
  obtain ⟨U', hU', V', hV', h1, h2, h3⟩ :=
    A4.prune E (ε * ℓ / 10) (δ * r / 10) _ U V rfl
  have hF := A4.F_full E U V hE
  have hU'nn : (0:ℝ) ≤ U'.card := Nat.cast_nonneg _
  have hV'nn : (0:ℝ) ≤ V'.card := Nat.cast_nonneg _
  have hlow : 4 / 5 * (E.card : ℝ) ≤ A4.F E U' V' := by
    have : 0 ≤ ε * ℓ / 10 * U'.card := by positivity
    have : 0 ≤ δ * r / 10 * V'.card := by positivity
    have e1 : ε * ℓ / 10 * U.card = E.card / 10 := by rw [hε]; ring
    have e2 : δ * r / 10 * V.card = E.card / 10 := by rw [hδ]; ring
    linarith
  have hupU : A4.F E U' V' ≤ ℓ * U'.card := by
    rw [A4.F_left]
    calc ∑ x ∈ U', ((V'.filter fun y => (x, y) ∈ E).card : ℝ)
        ≤ ∑ _x ∈ U', ℓ := by
          refine Finset.sum_le_sum fun x hx => ?_
          refine le_trans ?_ (hdegU x (hU' hx))
          have : (V'.filter fun y => (x, y) ∈ E).card ≤ (E.filter fun e => e.1 = x).card := by
            refine Finset.card_le_card_of_injOn (fun y => (x, y)) ?_ ?_
            · intro y hy
              simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter] at hy ⊢
              simp [hy.2]
            · intro y _ z _ h
              simpa using h
          exact_mod_cast this
      _ = ℓ * U'.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hupV : A4.F E U' V' ≤ r * V'.card := by
    rw [A4.F_right]
    calc ∑ y ∈ V', ((U'.filter fun x => (x, y) ∈ E).card : ℝ)
        ≤ ∑ _y ∈ V', r := by
          refine Finset.sum_le_sum fun y hy => ?_
          refine le_trans ?_ (hdegV y (hV' hy))
          have : (U'.filter fun x => (x, y) ∈ E).card ≤ (E.filter fun e => e.2 = y).card := by
            refine Finset.card_le_card_of_injOn (fun x => (x, y)) ?_ ?_
            · intro x hx
              simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter] at hx ⊢
              simp [hx.2]
            · intro x _ z _ h
              simpa using h
          exact_mod_cast this
      _ = r * V'.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  refine ⟨U', hU', V', hV', ?_, ?_, h1, h2⟩
  · have : ℓ * (4 * ε / 5 * U.card) ≤ ℓ * U'.card := by
      have : ℓ * (4 * ε / 5 * U.card) = 4 / 5 * (ε * ℓ * U.card) := by ring
      rw [this, ← hε]; linarith
    exact le_of_mul_le_mul_left this hℓ
  · have : r * (4 * δ / 5 * V.card) ≤ r * V'.card := by
      have : r * (4 * δ / 5 * V.card) = 4 / 5 * (δ * r * V.card) := by ring
      rw [this, ← hδ]; linarith
    exact le_of_mul_le_mul_left this hr

end DerandLDT

open DerandLDT in
theorem solution {α β : Type u} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) (E : Finset (α × β)) (hE : E ⊆ U ×ˢ V)
    (ℓ r : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r)
    (hdegU : ∀ u ∈ U, ((E.filter fun e => e.1 = u).card : ℝ) ≤ ℓ)
    (hdegV : ∀ v ∈ V, ((E.filter fun e => e.2 = v).card : ℝ) ≤ r)
    (ε δ : ℝ) (hε : (E.card : ℝ) = ε * ℓ * U.card) (hδ : (E.card : ℝ) = δ * r * V.card) :
    ∃ U' ⊆ U, ∃ V' ⊆ V,
      4 * ε / 5 * (U.card : ℝ) ≤ U'.card ∧ 4 * δ / 5 * (V.card : ℝ) ≤ V'.card ∧
      (∀ u ∈ U', ε * ℓ / 10 ≤ ((V'.filter fun v => (u, v) ∈ E).card : ℝ)) ∧
      (∀ v ∈ V', δ * r / 10 ≤ ((U'.filter fun u => (u, v) ∈ E).card : ℝ)) :=
  DerandLDT.lemma_3_18_main U V E hE ℓ r hℓ hr hdegU hdegV ε δ hε hδ
