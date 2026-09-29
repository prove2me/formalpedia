-- Prove2me | solution 1 for FamousTheorems.von_staudt_clausen
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:10:25.285978+00:00
-- url     : https://prove2.me/submissions/0800cdb1-52e9-4db9-8917-c1cfbff90783

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution (k : ℕ) :
    bernoulli (2 * k) + ∑ p ∈ Finset.range (2 * k + 2) with p.Prime ∧ (p - 1) ∣ 2 * k,
      (1 : ℚ) / p ∈ Set.range Int.cast := Bernoulli.vonStaudt_clausen k
