-- Prove2me | solution 1 for Freiman.lowerJ_contact_iterate_box
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:11:39.464622+00:00
-- url     : https://prove2.me/submissions/7e43b488-aee3-412d-b6ad-9a8b4bd6d8f3

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem iter_succ (k : ℕ) (x : ℝ) : lowerJIter (k+1) x = 1 / (3 + lowerJIter k x) := by
  unfold lowerJIter
  rw [List.replicate_succ]
  simp only [prefixEval]
  norm_num

theorem box_step (y lo hi : ℝ) (h1 : lo < y) (h2 : y < hi) (hlo : 0 < lo)
    (hphi1 : lo < 1/(3+hi)) (hphi2 : 1/(3+lo) < hi) : lo < 1/(3+y) ∧ 1/(3+y) < hi := by
  constructor
  · calc lo < 1/(3+hi) := hphi1
      _ < 1/(3+y) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
  · calc 1/(3+y) < 1/(3+lo) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
      _ < hi := hphi2

theorem solution (hn : lowerJSignFacts) (k : ℕ) (hk : 2 ≤ k) : (151/500:ℝ) < lowerJIter k lowerJA ∧ lowerJIter k lowerJA < (303/1000:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJD ∧ lowerJIter k lowerJD < (303/1000:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJC ∧ lowerJIter k lowerJC < (38/125:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJD ∧ lowerJIter k lowerJD < (38/125:ℝ) := by
  have s14 : lowerJSigns 14 = lowerJIter 2 lowerJA - 151/500 := rfl
  have s15 : lowerJSigns 15 = 303/1000 - lowerJIter 2 lowerJA := rfl
  have s16 : lowerJSigns 16 = lowerJIter 2 lowerJD - 151/500 := rfl
  have s17 : lowerJSigns 17 = 303/1000 - lowerJIter 2 lowerJD := rfl
  have s18 : lowerJSigns 18 = lowerJIter 2 lowerJC - 151/500 := rfl
  have s19 : lowerJSigns 19 = 38/125 - lowerJIter 2 lowerJC := rfl
  have s22 : lowerJSigns 22 = 1/(3+303/1000) - 151/500 := rfl
  have s23 : lowerJSigns 23 = 303/1000 - 1/(3+151/500) := rfl
  have s24 : lowerJSigns 24 = 1/(3+38/125) - 151/500 := rfl
  have s25 : lowerJSigns 25 = 38/125 - 1/(3+151/500) := rfl
  have h14 := hn 14; have h15 := hn 15; have h16 := hn 16; have h17 := hn 17
  have h18 := hn 18; have h19 := hn 19; have h22 := hn 22; have h23 := hn 23
  have h24 := hn 24; have h25 := hn 25
  rw [s14] at h14; rw [s15] at h15; rw [s16] at h16; rw [s17] at h17
  rw [s18] at h18; rw [s19] at h19; rw [s22] at h22; rw [s23] at h23
  rw [s24] at h24; rw [s25] at h25
  have p22 : (151/500:ℝ) < 1/(3+303/1000) := by linarith
  have p23 : 1/(3+151/500) < (303/1000:ℝ) := by linarith
  have p24 : (151/500:ℝ) < 1/(3+38/125) := by linarith
  have p25 : 1/(3+151/500) < (38/125:ℝ) := by linarith
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  | succ k hk ih =>
    obtain ⟨a1, a2, d1, d2, c1, c2, d3, d4⟩ := ih
    rw [iter_succ, iter_succ, iter_succ]
    have hA := box_step _ _ _ a1 a2 (by norm_num) p22 p23
    have hD := box_step _ _ _ d1 d2 (by norm_num) p22 p23
    have hC := box_step _ _ _ c1 c2 (by norm_num) p24 p25
    have hD' := box_step _ _ _ d3 d4 (by norm_num) p24 p25
    exact ⟨hA.1, hA.2, hD.1, hD.2, hC.1, hC.2, hD'.1, hD'.2⟩
