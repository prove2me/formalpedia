-- Prove2me | solution 1 for FamousTheorems.pepin_test
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:13:24.154883+00:00
-- url     : https://prove2.me/submissions/0c02cf76-33fb-445f-abb8-ed128994fc5b

import Mathlib

theorem solution (n : ℕ) (h : (3 : ZMod n.fermatNumber) ^ 2 ^ (2 ^ n - 1) = -1) : n.fermatNumber.Prime :=
  Nat.pepin_primality n h
