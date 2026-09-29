-- Prove2me | solution 1 for Freiman.cert_sqrt_bracket
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:34:27.905149+00:00
-- url     : https://prove2.me/submissions/2b91be39-c6c8-4d6f-820d-f50d7b306eb9

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
    ∀ n l u : ℝ, 0 ≤ l → 0 ≤ u → l^2 < n → n < u^2 → l < Real.sqrt n ∧ Real.sqrt n < u := by
  intro n l u hl hu hln hnu
  have hn : 0 ≤ n := le_trans (sq_nonneg l) hln.le
  have hs := Real.sqrt_nonneg n
  have he := Real.sq_sqrt hn
  constructor <;> nlinarith


#print axioms solution
