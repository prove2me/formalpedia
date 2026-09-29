-- Prove2me | solution 1 for Freiman.cert_diagonal_corners_from_field_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:59:35.049793+00:00
-- url     : https://prove2.me/submissions/469e71f7-de5e-4e01-91b4-209559f899e7

import Definitions.Def_Freiman_certDiagonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin

open Freiman
open scoped BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 12000000

open Freiman

theorem solution :
    (∀ z : CertField, (certFieldLower z:ℝ) ≤ certFieldVal z) → ∀ (w : CertDiagonalData), certDiagonalDataValid w → ∀ i j : Fin 2, 0 ≤ certFieldVal (w.corners i j) := by
  intro hb w hw i j
  have hc := hw.2.2.2.2.2.2 i j
  have hn : 0 ≤ certFieldLower (w.corners i j) := by
    rcases hc with ⟨hq, hc⟩
    by_cases hq0 : w.lowerBounds i j = 0
    · simpa only [hq0, if_true] using hc
    · have ht : w.lowerBounds i j < certFieldLower (w.corners i j) := by
        simpa only [if_neg hq0] using hc
      exact hq.trans ht.le
  exact le_trans (by exact_mod_cast hn) (hb _)
#print axioms solution
