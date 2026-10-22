-- Prove2me | solution 1 for CompOT.EntropicLimit.eq_4_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:59:39.639504+00:00
-- url     : https://prove2.me/submissions/a268dbdc-9eee-4ad0-9444-7dd9e8168865

import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs
set_option autoImplicit false

open CompOT.EntropicLimit in
theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ) (hε : 0 < ε)
    (P Q : Matrix (Fin n) (Fin m) ℝ)
    (hP : CompOT.Assignment.IsOptimalCoupling C a b P) (hQ : IsEntropicOptimal C a b ε Q) :
    0 ≤ CompOT.Assignment.frob C Q - CompOT.Assignment.frob C P ∧ CompOT.Assignment.frob C Q - CompOT.Assignment.frob C P ≤ ε * (entropy Q - entropy P) := by
  have h1 := hP.2 Q hQ.1
  have h2 := hQ.2 P hP.1
  unfold entObjective at h2
  constructor
  · linarith
  · nlinarith
