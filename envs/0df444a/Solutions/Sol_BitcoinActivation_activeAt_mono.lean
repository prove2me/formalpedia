-- Prove2me | solution 1 for BitcoinActivation.activeAt_mono
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:16.534351+00:00
-- url     : https://prove2.me/submissions/d31db766-3b27-44be-b2a8-294a60e7ba81

import Definitions.Def_BitcoinActivation

open BitcoinActivation

theorem solution (dep : BuriedDeployment) (h₁ h₂ : Nat) (h : h₁ ≤ h₂)
    (ha : BitcoinActivation.activeAt h₁ dep = true) : BitcoinActivation.activeAt h₂ dep = true := by
  unfold activeAt at *
  simp only [decide_eq_true_eq] at *
  omega
