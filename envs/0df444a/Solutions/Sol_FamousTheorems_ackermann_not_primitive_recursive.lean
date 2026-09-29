-- Prove2me | solution 1 for FamousTheorems.ackermann_not_primitive_recursive
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:48:27.069506+00:00
-- url     : https://prove2.me/submissions/9d163001-d09d-4a50-9e17-aa61a1beb5c5

import Mathlib

theorem solution : ¬Nat.Primrec fun n : ℕ => ack n n :=
  not_nat_primrec_ack_self
