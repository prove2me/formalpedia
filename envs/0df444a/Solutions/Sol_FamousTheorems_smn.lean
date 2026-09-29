-- Prove2me | solution 1 for FamousTheorems.smn
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:10:25.354251+00:00
-- url     : https://prove2.me/submissions/1d3937a4-5040-4f1d-915e-eef63f3a19c9

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution : ∃ f : Nat.Partrec.Code → ℕ → Nat.Partrec.Code, Computable₂ f ∧
    ∀ c n x, Nat.Partrec.Code.eval (f c n) x =
      Nat.Partrec.Code.eval c (Nat.pair n x) := Nat.Partrec.Code.smn
