-- Prove2me | solution 1 for BunkbedFalse.bunkbed_conjecture_false
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T17:04:21.517834+00:00
-- url     : https://prove2.me/submissions/dd7d9201-cf34-45bb-92ae-0eac9cc29610

import Theorems.Thm_BunkbedFalse_explicit_counterexample

open Bunkbed Bunkbed.Hyper SimpleGraph Finset

theorem solution : ¬ BunkbedConjecture := by
  intro h
  obtain ⟨E, T, u, v, -, -, hconn, hlt⟩ := BunkbedFalse.explicit_counterexample
  exact absurd hlt
    (not_lt.mpr (h (Fin 7222) E T (1 / 2) (by norm_num) (by norm_num) hconn u v))
