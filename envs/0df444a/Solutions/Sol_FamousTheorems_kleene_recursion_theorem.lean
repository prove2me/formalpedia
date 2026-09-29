-- Prove2me | solution 1 for FamousTheorems.kleene_recursion_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:12:49.727851+00:00
-- url     : https://prove2.me/submissions/a78c9ea0-8501-4015-bd85-2fdc6edcea23

import Mathlib

theorem solution {f : Nat.Partrec.Code → ℕ →. ℕ} (hf : Partrec₂ f) : ∃ c : Nat.Partrec.Code, c.eval = f c :=
  Nat.Partrec.Code.fixed_point₂ hf
