-- Prove2me | solution 1 for DOPriorityQueue.Construction.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-16T14:43:48.18791+00:00
-- url     : https://prove2.me/submissions/6f1dedfe-189c-48bc-9b4d-10c26bf9111f

import Mathlib

set_option autoImplicit false

namespace DOPriorityQueue.Construction

theorem lemma_5_2 (V B E : ℕ) (hV : 1 ≤ V) (live : Finset ℕ)
    (hlive : ∀ k ∈ live, 1 ≤ k ∧ k ≤ V) (Qhat : ℕ → ℤ)
    (hest : ∀ x, 1 ≤ x → x ≤ V →
      |Qhat x - ((live.filter (· ≤ x)).card : ℤ)| ≤ 2 * (E : ℤ)) :
    (∀ x, 1 ≤ x → x ≤ V → (B : ℤ) + 2 * E ≤ Qhat x →
      (∀ y, 1 ≤ y → y < x → Qhat y < (B : ℤ) + 2 * E) →
        B ≤ (live.filter (· ≤ x)).card ∧
          (live.filter (· ≤ x)).card ≤ B + 4 * E + 1) ∧
    ((∀ x, 1 ≤ x → x ≤ V → Qhat x < (B : ℤ) + 2 * E) →
      live.card < B + 4 * E) := by
  classical
  let q : ℕ → ℕ := fun x => (live.filter (· ≤ x)).card
  constructor
  · intro x hx1 hxV hthreshold hsmall
    have hestx : |Qhat x - (q x : ℤ)| ≤ 2 * (E : ℤ) := hest x hx1 hxV
    have herrorx := (abs_le.mp hestx).2
    have hlowerx : (B : ℤ) ≤ (q x : ℤ) := by omega
    constructor
    · exact_mod_cast hlowerx
    · by_cases hxone : x = 1
      · subst x
        have hsubset : live.filter (· ≤ 1) ⊆ ({1} : Finset ℕ) := by
          intro k hk
          simp only [Finset.mem_filter] at hk
          have hvalid := hlive k hk.1
          simp only [Finset.mem_singleton]
          omega
        have hqle : q 1 ≤ 1 := by
          change (live.filter (· ≤ 1)).card ≤ ({1} : Finset ℕ).card
          calc
            _ ≤ ({1} : Finset ℕ).card := Finset.card_le_card hsubset
            _ = 1 := by simp
        change q 1 ≤ B + 4 * E + 1
        omega
      · have hgreater : 1 < x := by omega
        let y := x - 1
        have hy1 : 1 ≤ y := by omega
        have hyx : y < x := by omega
        have hyV : y ≤ V := by omega
        have hsmallY := hsmall y hy1 hyx
        have hestY : |Qhat y - (q y : ℤ)| ≤ 2 * (E : ℤ) := hest y hy1 hyV
        have hYq : (q y : ℤ) < (B : ℤ) + 4 * (E : ℤ) := by
          have herrorY := (abs_le.mp hestY).1
          omega
        have hYqNat : q y < B + 4 * E := by exact_mod_cast hYq
        have hstep : q x ≤ q y + 1 := by
          have hsubset : live.filter (· ≤ x) ⊆ (live.filter (· ≤ y)) ∪ {x} := by
            intro k hk
            change k ∈ live.filter (· ≤ x) at hk
            simp only [Finset.mem_filter] at hk
            by_cases hkprev : k ≤ y
            · exact Finset.mem_union.mpr <| Or.inl (Finset.mem_filter.mpr ⟨hk.1, hkprev⟩)
            · have hkx : k = x := by omega
              subst k
              exact Finset.mem_union.mpr <| Or.inr (Finset.mem_singleton.mpr rfl)
          calc
            _ ≤ ((live.filter (· ≤ y)) ∪ {x}).card := Finset.card_le_card hsubset
            _ ≤ (live.filter (· ≤ y)).card + ({x} : Finset ℕ).card := Finset.card_union_le (live.filter (· ≤ y)) {x}
            _ = (live.filter (· ≤ y)).card + 1 := by simp
            _ = q y + 1 := rfl
        change q x ≤ B + 4 * E + 1
        omega
  · intro hbelow
    have hestV : |Qhat V - (q V : ℤ)| ≤ 2 * (E : ℤ) := hest V hV le_rfl
    have herrorV := (abs_le.mp hestV).1
    have hfilter : live.filter (· ≤ V) = live := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · exact And.left
      · intro hk
        exact ⟨hk, (hlive k hk).2⟩
    have hqV : q V = live.card := by
      dsimp [q]
      rw [hfilter]
    have hbound : (live.card : ℤ) < (B : ℤ) + 4 * (E : ℤ) := by
      rw [← hqV]
      have hbelowV := hbelow V hV le_rfl
      omega
    exact_mod_cast hbound

end DOPriorityQueue.Construction

open DOPriorityQueue.Construction

/-- Guo--Hong--Li, STOC 2027 submission #538 (October 2026), p. 21, Lemma 5.2.
`live` is the set of distinct encoded keys of live records in `[V] = {1, …, V}`,
`Q x = #{k ∈ live | k ≤ x}`, and `Qhat` is within `2E` of `Q` on `[V]`.
If `x ∈ [V]` is the smallest with `Qhat x ≥ B + 2E`, then `B ≤ Q x ≤ B + 4E + 1`;
if there is no such `x`, the total number of live records is below `B + 4E`. -/
theorem solution (V B E : ℕ) (hV : 1 ≤ V) (live : Finset ℕ)
    (hlive : ∀ k ∈ live, 1 ≤ k ∧ k ≤ V) (Qhat : ℕ → ℤ)
    (hest : ∀ x, 1 ≤ x → x ≤ V →
      |Qhat x - ((live.filter (· ≤ x)).card : ℤ)| ≤ 2 * (E : ℤ)) :
    (∀ x, 1 ≤ x → x ≤ V → (B : ℤ) + 2 * E ≤ Qhat x →
      (∀ y, 1 ≤ y → y < x → Qhat y < (B : ℤ) + 2 * E) →
        B ≤ (live.filter (· ≤ x)).card ∧
          (live.filter (· ≤ x)).card ≤ B + 4 * E + 1) ∧
    ((∀ x, 1 ≤ x → x ≤ V → Qhat x < (B : ℤ) + 2 * E) →
      live.card < B + 4 * E) := DOPriorityQueue.Construction.lemma_5_2 V B E hV live hlive Qhat hest


