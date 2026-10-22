-- Prove2me | solution 1 for DIGing.Undir.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:40:44.669995+00:00
-- url     : https://prove2.me/submissions/0de82674-e72f-4ceb-a650-6e9523a88499

import Mathlib
import Definitions.Def_DIGing_Undir_Common

set_option autoImplicit false

open DIGing.Undir

theorem solution {n p : ℕ} (s : ℕ → Stack n p) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (U : ℝ) (hU : ∀ k : ℕ, frob (s k) / lam ^ k ≤ U) :
    ∀ k : ℕ, frob (s k) ≤ U * lam ^ k := by
  intro k
  have h := hU k
  rwa [div_le_iff₀ (by positivity)] at h
