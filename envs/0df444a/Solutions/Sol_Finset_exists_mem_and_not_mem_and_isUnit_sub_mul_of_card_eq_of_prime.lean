-- Prove2me | solution 1 for Finset.exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e1cab9be-b741-575c-8ea5-1c176bfd6ffd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Finset_exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime

set_option autoImplicit false

theorem solution
    (q : ℕ) [Fact q.Prime] (S : Finset (ℕ × ℕ)) (hS : S ⊆ Finset.range q ×ˢ Finset.range q)
    (hcard : S.card = q) :
    ∃ a b c d : ℕ, (a, b) ∈ S ∧ c < q ∧ d < q ∧ (c, d) ∉ S ∧
      IsUnit (((a * d : ℤ) - (b * c : ℤ) : ℤ) : ZMod q) := by
  classical
  have hq : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hq.two_le

  have cast_inj : ∀ d d' : ℕ, d < q → d' < q → (d : ZMod q) = (d' : ZMod q) → d = d' := by
    intro d d' hd hd' h
    have h' := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd'] at h'
  have cast_ne : ∀ d : ℕ, d < q → d ≠ 0 → (d : ZMod q) ≠ 0 := by
    intro d hd hd0 h
    exact hd0 (cast_inj d 0 hd (by omega) (by rw [h, Nat.cast_zero]))

  obtain ⟨p, hpS, hp0⟩ : ∃ p ∈ S, p ≠ ((0, 0) : ℕ × ℕ) := by
    by_contra hcon
    push Not at hcon
    have hsub : S ⊆ {((0, 0) : ℕ × ℕ)} := fun x hx => Finset.mem_singleton.mpr (hcon x hx)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton, hcard] at hle
    omega
  obtain ⟨a, b⟩ := p
  have hab : (a, b) ∈ Finset.range q ×ˢ Finset.range q := hS hpS
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
  obtain ⟨ha, hb⟩ := hab

  set B : Finset (ℕ × ℕ) := Finset.range q ×ˢ Finset.range q with hB
  set L : Finset (ℕ × ℕ) := B.filter (fun p => (((a * p.2 : ℤ) - (b * p.1 : ℤ) : ℤ) : ZMod q) = 0) with hL
  have hBcard : B.card = q * q := by rw [hB, Finset.card_product, Finset.card_range]
  have memL : ∀ c d : ℕ, (c, d) ∈ L ↔ (c < q ∧ d < q) ∧ (a : ZMod q) * d = b * c := by
    intro c d
    simp only [hL, hB, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    push_cast
    rw [sub_eq_zero]

  have hLcard : L.card ≤ q := by
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    ·
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact hp0 (by rw [ha0])
      have hbq : (b : ZMod q) ≠ 0 := cast_ne b hb hb0
      have first_zero : ∀ c d : ℕ, (c, d) ∈ L → c = 0 := by
        intro c d h
        rw [memL] at h
        obtain ⟨⟨hc, hd⟩, h⟩ := h
        rw [ha0, Nat.cast_zero, zero_mul, eq_comm, mul_eq_zero] at h
        rcases h with h | h
        · exact absurd h hbq
        · exact cast_inj c 0 hc (by omega) (by rw [h, Nat.cast_zero])
      calc L.card ≤ (Finset.range q).card := by
            refine Finset.card_le_card_of_injOn (fun p => p.2) ?_ ?_
            · intro p hp
              obtain ⟨c, d⟩ := p
              exact Finset.mem_range.mpr ((memL c d).mp hp).1.2
            · rintro ⟨c, d⟩ hcd ⟨c', d'⟩ hcd' (h : d = d')
              have h1 := first_zero c d hcd
              have h2 := first_zero c' d' hcd'
              exact Prod.ext (h1.trans h2.symm) h
        _ = q := Finset.card_range q
    ·
      have haq : (a : ZMod q) ≠ 0 := cast_ne a ha (by omega)
      calc L.card ≤ (Finset.range q).card := by
            refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
            · intro p hp
              obtain ⟨c, d⟩ := p
              exact Finset.mem_range.mpr ((memL c d).mp hp).1.1
            · rintro ⟨c, d⟩ hcd ⟨c', d'⟩ hcd' (h : c = c')
              have h1 := (memL c d).mp hcd
              have h2 := (memL c' d').mp hcd'
              subst h
              have h3 : (a : ZMod q) * d = (a : ZMod q) * d' := h1.2.trans h2.2.symm
              have h4 : (d : ZMod q) = d' := mul_left_cancel₀ haq h3
              exact Prod.ext rfl (cast_inj d d' h1.1.2 h2.1.2 h4)
        _ = q := Finset.card_range q

  have hmemL : (a, b) ∈ L := (memL a b).mpr ⟨⟨ha, hb⟩, mul_comm _ _⟩
  have hsub : S ∪ L ⊆ B := Finset.union_subset hS (Finset.filter_subset _ _)
  have hlt : (S ∪ L).card < B.card := by
    have h1 : (S ∪ L).card + (S ∩ L).card = S.card + L.card := Finset.card_union_add_card_inter S L
    have h2 : 0 < (S ∩ L).card := Finset.card_pos.mpr ⟨(a, b), Finset.mem_inter.mpr ⟨hpS, hmemL⟩⟩
    have hqq : 2 * q ≤ B.card := by rw [hBcard]; exact Nat.mul_le_mul_right q hq2
    omega
  obtain ⟨x, hxB, hxSL⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨c, d⟩ := x
  have hcd : c < q ∧ d < q := by
    simpa only [hB, Finset.mem_product, Finset.mem_range] using hxB
  rw [Finset.mem_union, not_or] at hxSL
  obtain ⟨hxS, hxL⟩ := hxSL
  refine ⟨a, b, c, d, hpS, hcd.1, hcd.2, hxS, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0'
  apply hxL
  rw [memL]
  refine ⟨hcd, ?_⟩
  have h' : ((a : ZMod q) * d - b * c) = 0 := by
    have := h0'
    push_cast at this
    exact this
  exact sub_eq_zero.mp h'

end S_Finset_exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime
end P2MW
export P2MW.S_Finset_exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime (solution)
