-- Prove2me | solution 1 for FamousTheorems.rice_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:12:49.488038+00:00
-- url     : https://prove2.me/submissions/176c784e-8652-49ea-a39f-aafe165881f7

import Mathlib

theorem solution (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c : Nat.Partrec.Code => c.eval ∈ C) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C :=
  ComputablePred.rice C h hf hg fC
