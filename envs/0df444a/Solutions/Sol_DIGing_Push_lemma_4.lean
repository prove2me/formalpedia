-- Prove2me | solution 1 for DIGing.Push.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:46:21.889494+00:00
-- url     : https://prove2.me/submissions/e6403c38-b142-493c-80e2-d7d073b4c356

import Mathlib
import Definitions.Def_DIGing_Undir_Common

set_option autoImplicit false

theorem solution {n p : ℕ} (s : ℕ → DIGing.Undir.Stack n p) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (U : ℝ) (hU : ∀ k : ℕ, DIGing.Undir.frob (s k) / lam ^ k ≤ U) :
    ∀ k : ℕ, DIGing.Undir.frob (s k) ≤ U * lam ^ k := by
  intro k
  have h := hU k
  rwa [div_le_iff₀ (by positivity)] at h
