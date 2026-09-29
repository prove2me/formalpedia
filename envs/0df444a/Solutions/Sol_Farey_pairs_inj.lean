-- Prove2me | solution 1 for Farey.pairs_inj
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-10T10:51:17.672258+00:00
-- url     : https://prove2.me/submissions/9ea9963b-86ba-4616-b946-c7593f431236

import Definitions.Def_Farey
import Theorems.Thm_Farey_mem_pairs
import Mathlib

theorem solution {P : ℕ} {p p' : ℕ × ℕ} (hp : p ∈ Farey.pairs P) (hp' : p' ∈ Farey.pairs P)
    (h : (p.2 : ℝ) / (p.1 : ℝ) = (p'.2 : ℝ) / (p'.1 : ℝ)) : p = p' := by
  obtain ⟨hq1, -, ha1, haq, hcop⟩ := Farey.mem_pairs.mp hp
  obtain ⟨hq1', -, ha1', haq', hcop'⟩ := Farey.mem_pairs.mp hp'
  have hq : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hq1
  have hq' : (0 : ℝ) < (p'.1 : ℝ) := by exact_mod_cast hq1'
  rw [div_eq_div_iff hq.ne' hq'.ne'] at h
  have hN : p.2 * p'.1 = p'.2 * p.1 := by exact_mod_cast h
  have h1 : p.1 ∣ p'.1 := by
    have : p.1 ∣ p.2 * p'.1 := ⟨p'.2, by rw [hN, mul_comm]⟩
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
  have h2 : p'.1 ∣ p.1 := by
    have : p'.1 ∣ p'.2 * p.1 := ⟨p.2, by rw [← hN, mul_comm]⟩
    exact (Nat.Coprime.symm hcop').dvd_of_dvd_mul_left this
  have hqq : p.1 = p'.1 := Nat.dvd_antisymm h1 h2
  have haa : p.2 = p'.2 := by
    rw [hqq] at hN
    have hpos : (0 : ℕ) < p'.1 := by omega
    exact Nat.eq_of_mul_eq_mul_right hpos hN
  exact Prod.ext hqq haa
