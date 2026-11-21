-- Prove2me | solution 1 for CollatzMission.syracuse_odd_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-20T10:29:02.988511+00:00
-- url     : https://prove2.me/submissions/8e2bdbce-0188-40a2-a369-2c1f97be8d18
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CollatzMission_syracuse_descent_large_three_mod_four
import Theorems.Thm_syracuse_descends_below_2310000

open Nat

private theorem step_pos_odd (n : ℕ) : 0 < syracuseStep n ∧ ¬ Even (syracuseStep n) := by
  have hn : 3 * n + 1 ≠ 0 := by omega
  exact ⟨ordCompl_pos 2 hn, fun h => not_dvd_ordCompl prime_two hn (even_iff_two_dvd.mp h)⟩

private theorem orbit_pos_odd (n t : ℕ) (hn : 0 < n) (ho : ¬ Even n) :
    0 < syracuseStep^[t] n ∧ ¬ Even (syracuseStep^[t] n) := by
  cases t with
  | zero => exact ⟨hn, ho⟩
  | succ t =>
    rw [Function.iterate_succ_apply']
    exact step_pos_odd _

private theorem step_lt_of_mod_four_eq_one (n : ℕ) (hn : 1 < n) (hm : n % 4 = 1) :
    syracuseStep n < n := by
  have h : 2 ^ 2 ∣ (3 * n + 1) := by
    change 4 ∣ (3 * n + 1)
    omega
  have hq : 0 < (3 * n + 1) / 4 := by omega
  have hd := ordCompl_dvd ((3 * n + 1) / 4) 2
  have he := ordCompl_div_pow_of_dvd 2 prime_two h
  change ordCompl[2] ((3 * n + 1) / 4) = syracuseStep n at he
  rw [he] at hd
  have hb := le_of_dvd hq hd
  omega

theorem solution :
    ∀ n : ℕ, 0 < n → ¬ Even n → ∃ t : ℕ, syracuseStep^[t] n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn ho
    by_cases h1 : n = 1
    · exact ⟨0, h1⟩
    have hgt : 1 < n := by omega
    have hodd : Odd n := Nat.not_even_iff_odd.mp ho
    have hd : ∃ t : ℕ, syracuseStep^[t] n < n := by
      by_cases hb : n < 2310000
      · exact syracuse_descends_below_2310000 n hgt hb hodd
      by_cases hm : n % 4 = 1
      · exact ⟨1, by simpa using step_lt_of_mod_four_eq_one n hgt hm⟩
      · have hmod : n % 4 = 3 := by
          have h2 := Nat.odd_iff.mp hodd
          omega
        exact CollatzMission.syracuse_descent_large_three_mod_four n (by omega) hmod
    obtain ⟨t, ht⟩ := hd
    have hp := orbit_pos_odd n t hn ho
    obtain ⟨s, hs⟩ := ih _ ht hp.1 hp.2
    exact ⟨s + t, by simpa only [Function.iterate_add_apply] using hs⟩
