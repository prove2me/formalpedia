-- Prove2me | solution 1 for Freiman.lowerJ_contact_bulk
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:10:54.716216+00:00
-- url     : https://prove2.me/submissions/f66e72c0-cb7d-486e-924e-0f8b47488f47

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem solution (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) (k : ℕ) (hk : 2 ≤ k) (hf : (371/500:ℝ) < lowerJCoeff*(1+lowerJTau k*lowerJC)/(1+lowerJTau k*lowerJA)) (hb : (151/500:ℝ) < lowerJIter k lowerJA ∧ lowerJIter k lowerJA < (303/1000:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJD ∧ lowerJIter k lowerJD < (303/1000:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJC ∧ lowerJIter k lowerJC < (38/125:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJD ∧ lowerJIter k lowerJD < (38/125:ℝ)) : lowerJHBar r s < lowerJHK k r s := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨a1, a2, d1, d2, c1, c2, -, -⟩ := hb
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  unfold lowerJHBar lowerJHK lowerJH
  -- numerators and denominators
  have n1 : 0 ≤ (371/500:ℝ)*(1+s*(151/500)) := by nlinarith
  have n2 : 0 ≤ (1+s*(151/500):ℝ) := by nlinarith
  have hN : (371/500:ℝ)*(1+s*(151/500))*(1+s*(151/500)) <
      lowerJCoeff*(1+lowerJTau k*lowerJC)/(1+lowerJTau k*lowerJA)*(1+s*lowerJIter k lowerJC)*(1+s*lowerJIter k lowerJD) := by
    have e1 : (1+s*(151/500):ℝ) < 1+s*lowerJIter k lowerJC := by nlinarith
    have e2 : (1+s*(151/500):ℝ) < 1+s*lowerJIter k lowerJD := by nlinarith
    exact mul_lt_mul'' (mul_lt_mul'' hf e1 (by norm_num) n2) e2 n1 n2
  have hD : (1+r*lowerJIter k lowerJA)*(1+r*lowerJIter k lowerJD) <
      (1+r*(303/1000:ℝ))*(1+r*(303/1000:ℝ)) := by
    have e1 : 1+r*lowerJIter k lowerJA < (1+r*(303/1000):ℝ) := by nlinarith
    have e2 : 1+r*lowerJIter k lowerJD < (1+r*(303/1000):ℝ) := by nlinarith
    exact mul_lt_mul'' e1 e2 (by nlinarith) (by nlinarith)
  have pD1 : 0 < (1+r*(303/1000:ℝ))*(1+r*(303/1000:ℝ)) := by nlinarith
  have pD2 : 0 < (1+r*lowerJIter k lowerJA)*(1+r*lowerJIter k lowerJD) := by
    apply mul_pos <;> nlinarith
  rw [div_lt_div_iff₀ pD1 pD2]
  have hN0 : 0 ≤ (371/500:ℝ)*(1+s*(151/500))*(1+s*(151/500)) := by nlinarith
  exact mul_lt_mul'' hN hD hN0 pD2.le
