-- Prove2me | solution 1 for Erdos287.diagonal_count_for_merged_dispersion_shifts
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T20:26:22.551257+00:00
-- url     : https://prove2.me/submissions/160a7ae3-c733-4cee-94d0-127cbe9f929e

import Mathlib

open Finset

set_option autoImplicit false

private theorem fixed_products (u v n n' N L : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hL : 0 < L) (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ t ∈ T, t.1 ∣ u ∧ t.2.1 ∣ v ∧ t.2.2 ≤ 2 * N ∧
      L ≤ max t.1 t.2.1 ∧
      t.2.2 ≡ n [MOD t.1] ∧ t.2.2 ≡ n' [MOD t.2.1]) :
    T.card ≤ u.divisors.card * v.divisors.card * (2 * N / L + 1) := by
  let U := (u.divisors ×ˢ v.divisors) ×ˢ range (2 * N / L + 1)
  let encode (t : ℕ × ℕ × ℕ) := ((t.1, t.2.1), t.2.2 / max t.1 t.2.1)
  have hcard : T.card ≤ U.card := by
    apply card_le_card_of_injOn encode
    · intro t ht
      obtain ⟨ha, hb, hy, hmax, _, _⟩ := hT t ht
      refine mem_product.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Nat.mem_divisors.mpr ⟨ha, hu.ne'⟩
      · exact Nat.mem_divisors.mpr ⟨hb, hv.ne'⟩
      · apply mem_range.mpr
        exact Nat.lt_succ_of_le ((Nat.div_le_div_right hy).trans
          (Nat.div_le_div_left hmax hL))
    · rintro ⟨k, k', y⟩ hy ⟨l, l', z⟩ hz he
      change ((k, k'), y / max k k') = ((l, l'), z / max l l') at he
      have hkk := congrArg Prod.fst (congrArg Prod.fst he)
      have hk'k' := congrArg Prod.snd (congrArg Prod.fst he)
      have hqy := congrArg Prod.snd he
      change k = l at hkk
      change k' = l' at hk'k'
      subst l
      subst l'
      have hy' := hT (k, k', y) hy
      have hz' := hT (k, k', z) hz
      have hm : y % max k k' = z % max k k' := by
        rcases le_total k k' with h | h
        · simpa [max_eq_right h, Nat.ModEq] using hy'.2.2.2.2.2.trans hz'.2.2.2.2.2.symm
        · simpa [max_eq_left h, Nat.ModEq] using hy'.2.2.2.2.1.trans hz'.2.2.2.2.1.symm
      change y / max k k' = z / max k k' at hqy
      have hyz : y = z := by
        calc
          y = y % max k k' + max k k' * (y / max k k') := (Nat.mod_add_div _ _).symm
          _ = z % max k k' + max k k' * (z / max k k') := by rw [hm, hqy]
          _ = z := Nat.mod_add_div _ _
      exact congrArg (fun t => (k, k', t)) hyz
  simpa only [U, card_product, card_range] using hcard

/-- Counting the diagonal after absorbing the two matching shifts into
the Fourier frequencies. At least one shift is at least L. -/
theorem solution (n n' N L D C : ℕ) (hn : 0 < n) (hn' : 0 < n') (hL : 0 < L)
    (hC : ∀ u, 0 < u → u ≤ D → u.divisors.card ≤ C)
    (T : Finset ((ℕ × ℕ) × (ℕ × ℕ × ℕ)))
    (hT : ∀ t ∈ T, 0 < t.1.1 ∧ t.1.1 ≤ D ∧ 0 < t.1.2 ∧ t.1.2 ≤ D ∧
      t.1.1 * n' = t.1.2 * n ∧ t.2.1 ∣ t.1.1 ∧ t.2.2.1 ∣ t.1.2 ∧
      t.2.2.2 ≤ 2 * N ∧ L ≤ max t.2.1 t.2.2.1 ∧
      t.2.2.2 ≡ n [MOD t.2.1] ∧ t.2.2.2 ≡ n' [MOD t.2.2.1]) :
    T.card ≤ (D / (n' / n.gcd n')) * (C * C * (2 * N / L + 1)) := by
  let g := n.gcd n'
  let a := n / g
  let b := n' / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left n' hn
  have ha : a * g = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n n')
  have hb : b * g = n' := Nat.div_mul_cancel (Nat.gcd_dvd_right n n')
  have hb0 : 0 < b := Nat.pos_of_mul_pos_right (hb ▸ hn')
  have hcop : b.Coprime a := (Nat.coprime_div_gcd_div_gcd hg).symm
  let F := T.image Prod.fst
  have hparam (uv : ℕ × ℕ) (hF : uv ∈ F) :
      (uv.1 = a * (uv.2 / b) ∧ uv.2 = b * (uv.2 / b)) ∧
        0 < uv.2 / b ∧ uv.2 / b ≤ D / b := by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hF
    have h := hT t ht
    have hdet : t.1.1 * b = t.1.2 * a := by
      apply Nat.eq_of_mul_eq_mul_right hg
      simpa only [mul_assoc, ha, hb] using h.2.2.2.2.1
    have hd : b ∣ t.1.2 := hcop.dvd_of_dvd_mul_right
      (hdet ▸ dvd_mul_left b t.1.1)
    have he : t.1.2 = b * (t.1.2 / b) := by rw [mul_comm, Nat.div_mul_cancel hd]
    have hea : t.1.1 = a * (t.1.2 / b) := by
      apply Nat.eq_of_mul_eq_mul_right hb0
      calc
        t.1.1 * b = t.1.2 * a := hdet
        _ = (b * (t.1.2 / b)) * a := congrArg (fun u => u * a) he
        _ = (a * (t.1.2 / b)) * b := by ring
    exact ⟨⟨hea, he⟩, Nat.div_pos (Nat.le_of_dvd h.2.2.1 hd) hb0,
      Nat.div_le_div_right h.2.2.2.1⟩
  have hF : F.card ≤ D / b := by
    calc
      F.card ≤ (Icc 1 (D / b)).card := by
        apply card_le_card_of_injOn (fun uv : ℕ × ℕ => uv.2 / b)
        · intro uv huv
          refine mem_Icc.mpr ⟨(hparam uv huv).2.1, (hparam uv huv).2.2⟩
        · intro uv huv xy hxy he
          have huv' := (hparam uv huv).1
          have hxy' := (hparam xy hxy).1
          change uv.2 / b = xy.2 / b at he
          rw [he] at huv'
          exact Prod.ext (huv'.1.trans hxy'.1.symm) (huv'.2.trans hxy'.2.symm)
      _ = _ := by simp [Nat.card_Icc]
  have hfiber (uv : ℕ × ℕ) (huv : uv ∈ F) :
      (T.filter (fun t => t.1 = uv)).card ≤ C * C * (2 * N / L + 1) := by
    let A := T.filter (fun t => t.1 = uv)
    let B := A.image Prod.snd
    have hsize : B.card = A.card := by
      apply card_image_of_injOn
      intro x hx y hy he
      exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) he
    obtain ⟨p, hp, hr⟩ := mem_image.mp huv
    have hpT := hT p hp
    have hB : ∀ t ∈ B, t.1 ∣ uv.1 ∧ t.2.1 ∣ uv.2 ∧ t.2.2 ≤ 2 * N ∧
        L ≤ max t.1 t.2.1 ∧
        t.2.2 ≡ n [MOD t.1] ∧ t.2.2 ≡ n' [MOD t.2.1] := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
      have he := (mem_filter.mp ht).2
      rw [← he]
      exact (hT t (mem_filter.mp ht).1).2.2.2.2.2
    change A.card ≤ _
    rw [← hsize]
    calc
      _ ≤ uv.1.divisors.card * uv.2.divisors.card * (2 * N / L + 1) :=
        fixed_products uv.1 uv.2 n n' N L (hr ▸ hpT.1) (hr ▸ hpT.2.2.1) hL _ hB
      _ ≤ _ := Nat.mul_le_mul_right _
        (Nat.mul_le_mul (hC _ (hr ▸ hpT.1) (hr ▸ hpT.2.1))
          (hC _ (hr ▸ hpT.2.2.1) (hr ▸ hpT.2.2.2.1)))
  calc
    T.card = ∑ uv ∈ F, (T.filter (fun t => t.1 = uv)).card :=
      card_eq_sum_card_image Prod.fst T
    _ ≤ ∑ _uv ∈ F, C * C * (2 * N / L + 1) := sum_le_sum hfiber
    _ = F.card * (C * C * (2 * N / L + 1)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hF

