-- Prove2me | solution 1 for Erdos287.endpoint_extremal_cover_excludes_six_times_power_of_419
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:33:06.574279+00:00
-- url     : https://prove2.me/submissions/cbf8f8fa-8ffe-480c-8b0c-f62d0c8aa35a

import Mathlib
import Theorems.Thm_Erdos287_cofactor_cut_congruence
import Theorems.Thm_Erdos287_endpoint_extremal_cover_split_divisor_mass

open Finset

set_option autoImplicit false
set_option maxRecDepth 24000
set_option maxHeartbeats 3000000

private theorem splitResidue419 :
    ∀ C ∈ (Icc 6 17 : Finset ℕ).powerset,
      6 ∈ C → 10 ∈ C ∨ 15 ∈ C → ¬ 419 ∣ ∑ c ∈ C, 12252240 / c := by
  decide

/-- The split of the first denominator excludes the indicated 419-adic
endpoint family, even though its unsplit cofactor congruence is possible. -/
theorem solution (D : Finset ℕ) (M j : ℕ) (hj : 1 ≤ j) :
    let t := 419 ^ j
    let m := 6 * t
    m ∈ D → D ⊆ Finset.Icc m M →
    (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) →
    (∑ n ∈ D, (1 : ℚ) / n = 1) →
    (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m)) →
    15 * t ≤ M → M < 18 * t → False := by
  classical
  intro t m hmD hD hcover hsum hEnd hlow hhigh
  have ht : 0 < t := by dsimp [t]; positivity
  have hm : 1 < m := by dsimp [m]; omega
  have hpos (n : ℕ) (hn : n ∈ D) : 0 < n := hm.le.trans (mem_Icc.mp (hD hn)).1
  have hprod : (9 * t) * (4 * t) = m * m := by dsimp [m]; ring
  have hquot : m * m / (4 * t) = 9 * t := by rw [← hprod, Nat.mul_div_cancel _ (by omega)]
  have hB (d : ℕ) (hd : d ∈ ({4 * t} : Finset ℕ)) :
      0 < d ∧ d < m ∧ d ∣ m * m ∧ m + m * m / d ≤ M := by
    rw [mem_singleton] at hd
    subst d
    refine ⟨by omega, by dsimp [m]; omega, ⟨9 * t, hprod.symm.trans (mul_comm _ _)⟩, ?_⟩
    rw [hquot]
    dsimp [m]
    omega
  have hretain : 10 * t ∈ D ∨ 15 * t ∈ D := by
    have hh := (Erdos287.endpoint_extremal_cover_split_divisor_mass D {4 * t} m M
      hm hmD hD hcover hsum hEnd hB).1
    rw [card_singleton] at hh
    obtain ⟨n, hn⟩ := card_pos.mp hh
    obtain ⟨hnD, d, hd, hdn⟩ := mem_filter.mp hn
    rw [mem_singleton] at hd
    subst d
    rw [hquot] at hdn
    rcases hdn with rfl | rfl
    · left
      rwa [show 10 * t = m + 4 * t by dsimp [m]; omega]
    · right
      rwa [show 15 * t = m + 9 * t by dsimp [m]; omega]
  let F := D.filter (fun n => t ∣ n)
  let C := F.image (fun n => n / t)
  have hmem {c : ℕ} (hc : c * t ∈ D) : c ∈ C :=
    mem_image.mpr ⟨c * t, mem_filter.mpr ⟨hc, dvd_mul_left t c⟩, Nat.mul_div_cancel _ ht⟩
  have hRange {n : ℕ} (hn : n ∈ D) (hnd : t ∣ n) : n / t ∈ Icc 6 17 := by
    have hI := mem_Icc.mp (hD hn)
    have he : n / t * t = n := Nat.div_mul_cancel hnd
    have h₁ : 6 ≤ n / t := by
      by_contra! hlt
      have h := Nat.mul_lt_mul_of_pos_right hlt ht
      rw [he] at h
      exact hI.1.not_gt h
    have h₂ : n / t < 18 := Nat.lt_of_mul_lt_mul_right
      (show n / t * t < 18 * t by rw [he]; exact hI.2.trans_lt hhigh)
    exact mem_Icc.mpr ⟨h₁, by omega⟩
  have hC : C ⊆ Icc 6 17 := by
    intro c hc
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hc
    obtain ⟨hnD, hnd⟩ := mem_filter.mp hn
    exact hRange hnD hnd
  have hclears : ∀ c ∈ (Icc 6 17 : Finset ℕ), c ∣ 12252240 := by decide
  have hL (n : ℕ) (hn : n ∈ D) (hd : 419 ^ j ∣ n) : n / 419 ^ j ∣ 12252240 :=
    hclears _ (hRange hn hd)
  have H := Erdos287.cofactor_cut_congruence D 419 j 12252240 0 (by decide) hj hpos hsum hL (by simp)
  have hInj : Set.InjOn (fun n : ℕ => n / t) ↑F := by
    intro n hn p hp he
    have hnd : t ∣ n := (mem_filter.mp (show n ∈ F from hn)).2
    have hpd : t ∣ p := (mem_filter.mp (show p ∈ F from hp)).2
    have := congrArg (fun x : ℕ => x * t) he
    simpa only [Nat.div_mul_cancel hnd, Nat.div_mul_cancel hpd] using this
  have hNum : 419 ∣ ∑ c ∈ C, 12252240 / c := by
    rw [show C = F.image (fun n => n / t) from rfl, sum_image hInj]
    simpa only [zero_add, pow_one] using H
  exact splitResidue419 C (mem_powerset.mpr hC) (hmem hmD)
    (hretain.elim (fun h => Or.inl (hmem h)) (fun h => Or.inr (hmem h))) hNum

