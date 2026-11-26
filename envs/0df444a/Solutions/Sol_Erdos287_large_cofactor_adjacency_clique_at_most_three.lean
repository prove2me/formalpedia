-- Prove2me | solution 1 for Erdos287.large_cofactor_adjacency_clique_at_most_three
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:50:48.742519+00:00
-- url     : https://prove2.me/submissions/29fab68f-3471-4cb2-bc6a-bdb72be34792

import Mathlib
import Theorems.Thm_Erdos287_short_cofactor_cycles_balance

open Finset

set_option autoImplicit false

private theorem triangle_balance (r p q B u v w x y z : ℕ)
    (hr : 3 * B ^ 2 < r)
    (hu : u ≤ B) (hv : v ≤ B) (hw : w ≤ B) (hx : x ≤ B) (hy : y ≤ B) (hz : z ≤ B)
    (h₁ : |(u : ℤ) * r - (v : ℤ) * p| = 1)
    (h₂ : |(w : ℤ) * p - (x : ℤ) * q| = 1)
    (h₃ : |(y : ℤ) * q - (z : ℤ) * r| = 1) :
    u * w * y = v * x * z := by
  let a (i : ℕ) := if i = 0 then u else if i = 1 then w else y
  let b (i : ℕ) := if i = 0 then v else if i = 1 then x else z
  let s (i : ℕ) := if i = 1 then p else if i = 2 then q else r
  have hab : ∀ i < 3, a i ≤ B ∧ b i ≤ B := by
    intro i hi
    interval_cases i <;> simp [a, b, hu, hv, hw, hx, hy, hz]
  have hs : ∀ i < 3, |(a i : ℤ) * s i - (b i : ℤ) * s (i + 1)| = 1 := by
    intro i hi
    interval_cases i <;> simp [a, b, s, h₁, h₂, h₃]
  have hb := Erdos287.short_cofactor_cycles_balance a b s 3 B (by decide)
    (by simp [s]) (by simpa [s] using hr) hab hs
  simpa [prod_range_succ, a, b, mul_assoc] using hb

/-- Large factors whose multiple layers all meet in adjacent positions
form a clique of size at most three in an interval of ratio below three. -/
theorem solution (P : Finset ℕ) (a : ℕ → ℕ → ℕ) (m M B : ℕ)
    (hm : 0 < m) (hM : 2 ≤ M) (hRatio : M < 3 * m)
    (hP : ∀ p ∈ P, 3 * B ^ 2 < p)
    (hA : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      0 < a p q ∧ a p q ≤ B ∧ m ≤ a p q * p ∧ a p q * p ≤ M)
    (hE : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      a p q * p + 1 = a q p * q ∨ a q p * q + 1 = a p q * p) :
    P.card ≤ 3 := by
  classical
  rcases P.eq_empty_or_nonempty with rfl | hPN
  · simp
  obtain ⟨root, hroot⟩ := hPN
  have hpos (p : ℕ) (hp : p ∈ P) : 0 < p := (Nat.zero_le _).trans_lt (hP p hp)
  have hq (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq' : q ∈ P) (hne : p ≠ q) :
      (0 : ℚ) < a p q := by exact_mod_cast (hA p hp q hq' hne).1
  let s (p : ℕ) : ℚ := if p = root then 1 else (a root p : ℚ) / (a p root : ℚ)
  let t (p : ℕ) : ℚ := (p : ℚ) / s p
  have hs (p : ℕ) (hp : p ∈ P) : 0 < s p := by
    by_cases he : p = root
    · simp [s, he]
    · simpa only [s, if_neg he] using
        div_pos (hq root hroot p hp (Ne.symm he)) (hq p hp root hroot he)
  have ht (p : ℕ) (hp : p ∈ P) : 0 < t p := div_pos (by exact_mod_cast hpos p hp) (hs p hp)
  have habs (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) (hne : p ≠ q) :
      |(a p q : ℤ) * p - (a q p : ℤ) * q| = 1 := by
    rcases hE p hp q hq hne with h | h
    · have hh : (a p q : ℤ) * p + 1 = (a q p : ℤ) * q := by exact_mod_cast h
      rw [show (a p q : ℤ) * p - (a q p : ℤ) * q = -1 by linarith only [hh]]
      norm_num
    · have hh : (a q p : ℤ) * q + 1 = (a p q : ℤ) * p := by exact_mod_cast h
      rw [show (a p q : ℤ) * p - (a q p : ℤ) * q = 1 by linarith only [hh]]
      norm_num
  have hrootScale (p : ℕ) (hp : p ∈ P) (hpr : p ≠ root) :
      (a root p : ℚ) * s root = (a p root : ℚ) * s p := by
    simp only [s, if_pos rfl, if_neg hpr, mul_one]
    field_simp [(hq p hp root hroot hpr).ne']
  have hscale (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq' : q ∈ P) (hne : p ≠ q) :
      (a p q : ℚ) * s p = (a q p : ℚ) * s q := by
    by_cases hpr : p = root
    · subst p
      exact hrootScale q hq' hne.symm
    by_cases hqr : q = root
    · subst q
      exact (hrootScale p hp hne).symm
    have hb := triangle_balance root p q B
      (a root p) (a p root) (a p q) (a q p) (a q root) (a root q)
      (hP root hroot) (hA root hroot p hp (Ne.symm hpr)).2.1 (hA p hp root hroot hpr).2.1
      (hA p hp q hq' hne).2.1 (hA q hq' p hp hne.symm).2.1
      (hA q hq' root hroot hqr).2.1 (hA root hroot q hq' (Ne.symm hqr)).2.1
      (habs root hroot p hp (Ne.symm hpr)) (habs p hp q hq' hne) (habs q hq' root hroot hqr)
    have hb' : (a root p : ℚ) * a p q * a q root = (a p root : ℚ) * a q p * a root q := by
      exact_mod_cast hb
    simp only [s, if_neg hpr, if_neg hqr]
    field_simp [(hq p hp root hroot hpr).ne', (hq q hq' root hroot hqr).ne']
    linear_combination hb'
  have hedge (p : ℕ) (hp : p ∈ P) (q : ℕ) (hpq : q ∈ P) (hne : p ≠ q) (hord : t p ≤ t q) :
      ∃ x : ℕ, m ≤ x ∧ x ≤ M - 1 ∧ (t q - t p) * (x : ℚ) = t p := by
    let x := a p q * p
    let y := a q p * q
    let L := (a p q : ℚ) * s p
    have hL : 0 < L := mul_pos (hq p hp q hpq hne) (hs p hp)
    have htq (j : ℕ) (hj : j ∈ P) : s j * t j = j := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ (hs j hj).ne'
    have hx : (x : ℚ) = L * t p := by simp only [x, L, Nat.cast_mul, mul_assoc, htq p hp]
    have hy : (y : ℚ) = L * t q := by
      rw [show L = (a q p : ℚ) * s q from hscale p hp q hpq hne]
      simp only [y, Nat.cast_mul, mul_assoc, htq q hpq]
    have hxy : x ≤ y := by
      have h : (x : ℚ) ≤ y := by
        rw [hx, hy]
        exact mul_le_mul_of_nonneg_left hord hL.le
      exact_mod_cast h
    have hsucc : x + 1 = y := by
      rcases hE p hp q hpq hne with h | h
      · exact h
      · change y + 1 = x at h
        omega
    have hd : L * (t q - t p) = 1 := by
      have h : (x : ℚ) + 1 = y := by exact_mod_cast hsucc
      rw [hx, hy] at h
      linarith only [h]
    have hyM : y ≤ M := (hA q hpq p hp hne.symm).2.2.2
    refine ⟨x, (hA p hp q hpq hne).2.2.1, by omega, ?_⟩
    rw [hx]
    calc
      (t q - t p) * (L * t p) = (L * (t q - t p)) * t p := by ring
      _ = _ := by rw [hd, one_mul]
  let U := P.image t
  have hU : U.Nonempty := ⟨t root, mem_image_of_mem t hroot⟩
  let low := U.min' hU
  obtain ⟨v, hv, htv⟩ := mem_image.mp (min'_mem U hU)
  have hvlow : t v = low := htv
  have hlow : 0 < low := by rw [← hvlow]; exact ht v hv
  have htlow (p : ℕ) (hp : p ∈ P) : low ≤ t p := min'_le U _ (mem_image_of_mem t hp)
  let f (p : ℕ) : ℚ := (((M - 1 : ℕ) : ℚ) * (t p - low)) / low
  have hnonneg (p : ℕ) (hp : p ∈ P) : 0 ≤ f p :=
    div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (htlow p hp))) hlow.le
  have hlt (p : ℕ) (hp : p ∈ P) : f p < 3 := by
    by_cases he : v = p
    · subst p
      simp only [f, hvlow, sub_self, mul_zero, zero_div]
      norm_num
    · have ho : t v ≤ t p := by rw [hvlow]; exact htlow p hp
      obtain ⟨x, hxm, hxM, heq⟩ := hedge v hv p hp he ho
      rw [hvlow] at heq
      have hxpos : (0 : ℚ) < x := by exact_mod_cast hm.trans_le hxm
      have hf : f p = ((M - 1 : ℕ) : ℚ) / x := by
        apply (div_eq_div_iff hlow.ne' hxpos.ne').mpr
        rw [mul_assoc, heq]
      rw [hf]
      exact (div_lt_iff₀ hxpos).mpr (by exact_mod_cast (show M - 1 < 3 * x by omega))
  have hdist (p : ℕ) (hp : p ∈ P) (q : ℕ) (hpq : q ∈ P) (hne : p ≠ q)
      (hord : t p ≤ t q) : f p + 1 ≤ f q := by
    obtain ⟨x, hxm, hxM, hd⟩ := hedge p hp q hpq hne hord
    have hprod : low ≤ ((M - 1 : ℕ) : ℚ) * (t q - t p) := by
      calc
        low ≤ t p := htlow p hp
        _ = (x : ℚ) * (t q - t p) := by rw [mul_comm, hd]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hxM) (sub_nonneg.mpr hord)
    have hdiv := (le_div_iff₀ hlow).mpr (show (1 : ℚ) * low ≤ _ by simpa using hprod)
    have he : (((M - 1 : ℕ) : ℚ) * (t q - t p)) / low = f q - f p := by
      dsimp [f]
      ring
    rw [he] at hdiv
    linarith only [hdiv]
  let bin (p : ℕ) : ℤ := ⌊f p⌋
  have hmaps : Set.MapsTo bin (↑P : Set ℕ) (↑(Icc (0 : ℤ) 2) : Set ℤ) := by
    intro p hp
    have hu : bin p < (3 : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hlt p hp)
    exact mem_Icc.mpr ⟨Int.floor_nonneg.mpr (hnonneg p hp), by omega⟩
  have hbin : Set.InjOn bin (↑P : Set ℕ) := by
    intro p hp q hq' he
    by_contra hne
    have helper (u : ℕ) (hu : u ∈ P) (v : ℕ) (hv : v ∈ P)
        (hn : u ≠ v) (ho : t u ≤ t v) (hb : bin u = bin v) : False := by
      have hl : (bin u : ℚ) ≤ f u := Int.floor_le _
      have hr : f v < (bin u : ℚ) + 1 := by rw [hb]; exact Int.lt_floor_add_one _
      linarith only [hl, hr, hdist u hu v hv hn ho]
    rcases le_total (t p) (t q) with h | h
    · exact helper p hp q hq' hne h he
    · exact helper q hq' p hp (Ne.symm hne) h he.symm
  have hc := card_le_card_of_injOn bin hmaps hbin
  simpa using hc

