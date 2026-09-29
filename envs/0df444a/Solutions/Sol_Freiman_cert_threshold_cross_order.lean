-- Prove2me | solution 1 for Freiman.cert_threshold_cross_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:35:07.272386+00:00
-- url     : https://prove2.me/submissions/3999c01f-e3dc-4b44-952b-1220ccfdd6cf

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
    ∀ (l u : CertThreshold) (r s : ℝ), 0 < certThresholdDen l r → 0 < certThresholdDen u r →
    (0 ≤ certThresholdNum l s*certThresholdDen u r-certThresholdNum u s*certThresholdDen l r ↔ certThresholdVal u r s ≤ certThresholdVal l r s) ∧
    (0 < certThresholdNum l s*certThresholdDen u r-certThresholdNum u s*certThresholdDen l r ↔ certThresholdVal u r s < certThresholdVal l r s) := by
  intro l u r s hl hu
  unfold certThresholdVal
  constructor
  · rw [div_le_div_iff₀ hu hl]
    constructor <;> intro h <;> nlinarith
  · rw [div_lt_div_iff₀ hu hl]
    constructor <;> intro h <;> nlinarith


#print axioms solution
