-- Prove2me | solution 1 for Freiman.cert_threshold_denominator_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:34:47.483134+00:00
-- url     : https://prove2.me/submissions/e2cfcbbf-2f05-4c47-8fd2-901ce8c6b3bf

import Definitions.Def_Freiman_certificates
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

open Freiman
open scoped BigOperators


theorem solution :
    ∀ (t : CertThreshold) (r : ℝ), 0 ≤ r → 0 ≤ certFieldVal t.x0 → 0 ≤ certFieldVal t.x1 → 0 < certThresholdDen t r := by
  intro t r hr h0 h1
  exact mul_pos (by nlinarith [mul_nonneg hr h0])
    (by nlinarith [mul_nonneg hr h1])


#print axioms solution
