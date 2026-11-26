-- Prove2me | solution 1 for Erdos287.high_cofactor_exclusions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:21:44.163408+00:00
-- url     : https://prove2.me/submissions/ba1658bc-3857-492b-9003-5089e9b368a3

import Mathlib
import Theorems.Thm_Erdos287_short_cofactor_layer

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem large_dyadic_layer_empty (D : Finset ℕ) (m M e : ℕ) (hm : 0 < m)
    (he : 1 ≤ e) (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hupper : M < 5 * 2 ^ e) (hratio : M < 3 * m) :
    D.filter (fun n => 2 ^ e ∣ n) = ∅ := by
  let q : ℕ := 2 ^ e
  change M < 5 * q at hupper
  have hhi (n : ℕ) (hn : n ∈ D) : n ≤ M := (mem_Icc.mp (hD hn)).2
  have hlo (n : ℕ) (hn : n ∈ D) : m ≤ n := (mem_Icc.mp (hD hn)).1
  have hdouble : D.filter (fun n => (2 * q) ∣ n) = ∅ := by
    have hpow : (2 : ℕ) ^ (e + 1) = 2 * q := pow_succ' _ _
    have hwindow (a b : ℕ) (_ : m ≤ a * (2 * q)) (hb : b * (2 * q) ≤ M) : b ≤ a + 2 := by
      have hb' : b < 3 := Nat.lt_of_mul_lt_mul_right
        (hb.trans_lt (by omega : M < 3 * (2 * q)))
      omega
    have hshort := Erdos287.short_cofactor_layer D m M 2 (e + 1) hm (by decide) (by omega)
      hD hsum (by simpa only [hpow] using hwindow)
    dsimp only at hshort
    rw [hpow] at hshort
    rcases hshort with h | ⟨c, hc, hs⟩
    · exact h
    · have hbad (hh : (c + 2) * (2 * q) ∈ D) : False := by
        have hb' : c + 2 < 3 := Nat.lt_of_mul_lt_mul_right
          ((hhi _ hh).trans_lt (by omega : M < 3 * (2 * q)))
        omega
      rcases hs with ⟨_, hd⟩ | ⟨hshape, _⟩ | ⟨hshape, _⟩
      · omega
      · exact (hbad (mem_filter.mp (by rw [hshape]; simp)).1).elim
      · exact (hbad (mem_filter.mp (by rw [hshape]; simp)).1).elim
  have hwindow (a b : ℕ) (ha : m ≤ a * q) (hb : b * q ≤ M) : b ≤ a + 2 := by
    have hb' : b < 5 := Nat.lt_of_mul_lt_mul_right (hb.trans_lt hupper)
    by_cases ha' : a ≤ 1
    · have hmq : m ≤ q := ha.trans (by simpa using Nat.mul_le_mul_right q ha')
      have hb'' : b < 3 := Nat.lt_of_mul_lt_mul_right (hb.trans_lt (by omega : M < 3 * q))
      omega
    · omega
  rcases Erdos287.short_cofactor_layer D m M 2 e hm (by decide) he hD hsum hwindow with
    h | ⟨c, hc, hs⟩
  · exact h
  · have hbad (ha : c * q ∈ D) (hb : (c + 2) * q ∈ D) : False := by
      have hb' : c + 2 < 5 := Nat.lt_of_mul_lt_mul_right ((hhi _ hb).trans_lt hupper)
      have hc' : c = 1 ∨ c = 2 := by omega
      rcases hc' with rfl | rfl
      · simp only [one_mul, show 1 + 2 = (3 : ℕ) by decide] at ha hb
        have h1 := hlo _ ha
        have h3 := hhi _ hb
        omega
      · have hh : 2 * q ∈ D.filter (fun n => (2 * q) ∣ n) :=
          mem_filter.mpr ⟨ha, dvd_refl _⟩
        simpa only [hdouble, notMem_empty] using hh
    rcases hs with ⟨_, hd⟩ | ⟨hshape, _⟩ | ⟨hshape, _⟩
    · omega
    · exact (hbad (mem_filter.mp (by rw [hshape]; simp [q])).1
        (mem_filter.mp (by rw [hshape]; simp [q])).1).elim
    · exact (hbad (mem_filter.mp (by rw [hshape]; simp [q])).1
        (mem_filter.mp (by rw [hshape]; simp [q])).1).elim

private theorem prime_candidates (p c : ℕ) (hp : p.Prime) (hc : 0 < c) (hc' : c ≤ 4)
    (htest : p ∣ 2 * c + 1 ∨ c ≤ 3 ∧ (p ∣ 2 * c + 2 ∨ p ∣ 3 * c ^ 2 + 6 * c + 2)) :
    p ∈ ({2, 3, 5, 7, 11, 13, 47} : Finset ℕ) := by
  have hp' : p ≤ 47 := by
    rcases htest with h | ⟨h3, h | h⟩
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · have hbound : 3 * c ^ 2 + 6 * c + 2 ≤ 47 := by
        interval_cases c <;> decide
      exact (Nat.le_of_dvd (by positivity) h).trans hbound
  have hcheck : ∀ p ∈ Icc (2 : ℕ) 47, ∀ c ∈ Icc (1 : ℕ) 4, p.Prime →
      (p ∣ 2 * c + 1 ∨ c ≤ 3 ∧ (p ∣ 2 * c + 2 ∨ p ∣ 3 * c ^ 2 + 6 * c + 2)) →
      p ∈ ({2, 3, 5, 7, 11, 13, 47} : Finset ℕ) := by decide
  exact hcheck p (mem_Icc.mpr ⟨hp.two_le, hp'⟩) c (mem_Icc.mpr ⟨hc, hc'⟩) hp htest

/-- Above the diameter thresholds, dense dyadic layers are empty and a
nonempty large prime-power layer has its prime in a fixed seven-element set. -/
theorem solution (D : Finset ℕ) (m M : ℕ) (hm : 0 < m)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) :
    (∀ e : ℕ, 1 ≤ e → M < 3 * m → M < 5 * 2 ^ e →
      D.filter (fun n => 2 ^ e ∣ n) = ∅) ∧
    (∀ p e : ℕ, p.Prime → 1 ≤ e → 2 * m ≤ M → M < m + 3 * p ^ e →
      p ∉ ({2, 3, 5, 7, 11, 13, 47} : Finset ℕ) →
        D.filter (fun n => p ^ e ∣ n) = ∅) := by
  refine ⟨fun e he hratio hupper =>
    large_dyadic_layer_empty D m M e hm he hD hsum hupper hratio, ?_⟩
  intro p e hp he hratio hspan hpnot
  let q := p ^ e
  change M < m + 3 * q at hspan
  change D.filter (fun n => q ∣ n) = ∅
  have hwindow (a b : ℕ) (ha : m ≤ a * q) (hb : b * q ≤ M) : b ≤ a + 2 := by
    have hscale : b * q < (a + 3) * q := by rw [add_mul]; omega
    have h : b < a + 3 := Nat.lt_of_mul_lt_mul_right hscale
    omega
  rcases Erdos287.short_cofactor_layer D m M p e hm hp he hD hsum hwindow with
    h | ⟨c, hc, hs⟩
  · exact h
  · have hup (b : ℕ) (hb : b * q ∈ D.filter (fun n => q ∣ n)) : b < 6 := by
      apply Nat.lt_of_mul_lt_mul_right
      exact (mem_Icc.mp (hD (mem_filter.mp hb).1)).2.trans_lt (by omega : M < 6 * q)
    exfalso
    apply hpnot
    rcases hs with ⟨hpair, hd⟩ | ⟨hpair, hd⟩ | ⟨htriple, hd⟩
    · have h := hup (c + 1) (by rw [hpair]; simp [q])
      exact prime_candidates p c hp hc (by omega) (Or.inl hd)
    · have h := hup (c + 2) (by rw [hpair]; simp [q])
      exact prime_candidates p c hp hc (by omega) (Or.inr ⟨by omega, Or.inl hd⟩)
    · have h := hup (c + 2) (by rw [htriple]; simp [q])
      exact prime_candidates p c hp hc (by omega) (Or.inr ⟨by omega, Or.inr hd⟩)

