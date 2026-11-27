-- Prove2me | solution 1 for Erdos287.min_card_reciprocal_merge_omission_mass
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:48:31.155917+00:00
-- url     : https://prove2.me/submissions/2d4c845e-96dc-4173-9d97-0f01546e166a

import Mathlib
import Theorems.Thm_Erdos287_min_card_reciprocal_merge_obstruction

open Finset

set_option autoImplicit false

/-- Scaled copies of a two-term identity with separated input bands force
distinct blocking omissions and a lower bound on their reciprocal mass. -/
theorem solution (D T : Finset ℕ) (m M l u : ℕ)
    (hm : m ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hmin : ∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
      (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card)
    (a b c : ℕ) (hA : 3 ≤ a) (hAB : a + 2 ≤ b) (hCA : c < a)
    (hidentity : (1 : ℚ) / a + 1 / b = 1 / c)
    (hl : 0 < l) (hsep : a * u + 2 < b * l)
    (hT : ∀ t ∈ T, l ≤ t ∧ t ≤ u ∧ m ≤ c * t ∧ b * t ≤ M) :
    let L := T.filter (fun t => c * t ∉ D)
    let H := (Finset.Icc m M).filter (fun n => n ∉ D ∧
      ((a * l ≤ n + 1 ∧ n ≤ a * u + 1) ∨
        (b * l ≤ n + 1 ∧ n ≤ b * u + 1)))
    L.card ≤ H.card ∧
      (∑ t ∈ L, (1 : ℚ) / ((b * t + 1 : ℕ) : ℚ)) ≤
        ∑ n ∈ H, (1 : ℚ) / n := by
  classical
  intro L H
  let near (t n : ℕ) : Prop :=
    (a * t ≤ n + 1 ∧ n ≤ a * t + 1) ∨
      (b * t ≤ n + 1 ∧ n ≤ b * t + 1)
  have bounds (t : ℕ) (ht : t ∈ L) :
      l ≤ t ∧ t ≤ u ∧ m ≤ c * t ∧ b * t ≤ M :=
    hT t (mem_filter.mp ht).1
  have toHole (t n : ℕ) (ht : t ∈ L) (hn : n ∈ Icc m M)
      (hnD : n ∉ D) (hnear : near t n) : n ∈ H := by
    obtain ⟨hlt, htu, _, _⟩ := bounds t ht
    refine mem_filter.mpr ⟨hn, hnD, ?_⟩
    rcases hnear with h | h
    · exact Or.inl ⟨(Nat.mul_le_mul_left a hlt).trans h.1,
        h.2.trans (Nat.add_le_add_right (Nat.mul_le_mul_left a htu) 1)⟩
    · exact Or.inr ⟨(Nat.mul_le_mul_left b hlt).trans h.1,
        h.2.trans (Nat.add_le_add_right (Nat.mul_le_mul_left b htu) 1)⟩
  have hex (t : ℕ) : ∃ n, t ∈ L → n ∈ H ∧ near t n := by
    by_cases ht : t ∈ L
    · obtain ⟨hlt, htu, hmt, htM⟩ := bounds t ht
      have htpos : 0 < t := hl.trans_le hlt
      have hcD : c * t ∉ D := (mem_filter.mp ht).2
      have hcA : c * t < a * t := Nat.mul_lt_mul_of_pos_right hCA htpos
      have hlow : m < a * t := hmt.trans_lt hcA
      have hdist : a * t + 2 ≤ b * t := by
        have h := Nat.mul_le_mul_right t hAB
        rw [Nat.add_mul] at h
        omega
      have haRange : a * t ∈ Icc m M := mem_Icc.mpr ⟨by omega, by omega⟩
      have hbRange : b * t ∈ Icc m M := mem_Icc.mpr ⟨by omega, htM⟩
      by_cases ha : a * t ∈ D
      · by_cases hb : b * t ∈ D
        · have heq : (1 : ℚ) / ((a * t : ℕ) : ℚ) +
              1 / ((b * t : ℕ) : ℚ) = 1 / ((c * t : ℕ) : ℚ) := by
            push_cast
            simp only [div_eq_mul_inv, one_mul, mul_inv_rev] at hidentity ⊢
            rw [← mul_add, hidentity]
          obtain ⟨n, hn, hnD, _, hnNear⟩ := Erdos287.min_card_reciprocal_merge_obstruction
            D m M (a * t) (b * t) (c * t) hm hD hcover hsum hmin
            ha hb hlow hdist (mem_Icc.mpr ⟨hmt, by omega⟩) hcD heq
          have hn' : near t n := by
            rcases hnNear with h | h | h | h
            · exact Or.inl ⟨by omega, by omega⟩
            · exact Or.inl ⟨by omega, by omega⟩
            · exact Or.inr ⟨by omega, by omega⟩
            · exact Or.inr ⟨by omega, by omega⟩
          exact ⟨n, fun _ => ⟨toHole t n ht hn hnD hn', hn'⟩⟩
        · have hnear : near t (b * t) := Or.inr ⟨by omega, by omega⟩
          exact ⟨b * t, fun _ => ⟨toHole t _ ht hbRange hb hnear, hnear⟩⟩
      · have hnear : near t (a * t) := Or.inl ⟨by omega, by omega⟩
        exact ⟨a * t, fun _ => ⟨toHole t _ ht haRange ha hnear, hnear⟩⟩
    · exact ⟨0, fun ht' => (ht ht').elim⟩
  choose f hf using hex
  have hsub : L.image f ⊆ H := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hn
    exact (hf t ht).1
  have separated (d s t n : ℕ) (hd : 3 ≤ d)
      (hs : d * s ≤ n + 1 ∧ n ≤ d * s + 1)
      (ht : d * t ≤ n + 1 ∧ n ≤ d * t + 1) : s = t := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hmul := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at hmul
      omega
    · have hmul := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at hmul
      omega
  have hInj : Set.InjOn f ↑L := by
    intro s hs t ht he
    obtain ⟨hls, hsu, _, _⟩ := bounds s hs
    obtain ⟨hlt, htu, _, _⟩ := bounds t ht
    have hs' := (hf s hs).2
    have ht' := (hf t ht).2
    rw [he] at hs'
    rcases hs' with h₁ | h₁ <;> rcases ht' with h₂ | h₂
    · exact separated a s t (f t) hA h₁ h₂
    · have ha := Nat.mul_le_mul_left a hsu
      have hb := Nat.mul_le_mul_left b hlt
      omega
    · have ha := Nat.mul_le_mul_left a htu
      have hb := Nat.mul_le_mul_left b hls
      omega
    · exact separated b s t (f t) (by omega) h₁ h₂
  constructor
  · rw [← card_image_of_injOn hInj]
    exact card_le_card hsub
  · calc
      ∑ t ∈ L, (1 : ℚ) / ((b * t + 1 : ℕ) : ℚ) ≤
          ∑ t ∈ L, (1 : ℚ) / (f t : ℚ) := by
        apply sum_le_sum
        intro t ht
        obtain ⟨hlt, _, _, _⟩ := bounds t ht
        have hn := (hf t ht).2
        have ha := Nat.mul_le_mul_right t (show a ≤ b by omega)
        have ha2 := Nat.mul_le_mul_right t (show 3 ≤ a from hA)
        rw [show (3 : ℕ) * t = t + t + t by omega] at ha2
        have hpos : 0 < f t := by rcases hn with h | h <;> omega
        have hle : f t ≤ b * t + 1 := by rcases hn with h | h <;> omega
        exact one_div_le_one_div_of_le (by exact_mod_cast hpos) (by exact_mod_cast hle)
      _ = (∑ n ∈ L.image f, (1 : ℚ) / n) := by
        rw [sum_image hInj]
      _ ≤ (∑ n ∈ H, (1 : ℚ) / n) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _
        positivity

