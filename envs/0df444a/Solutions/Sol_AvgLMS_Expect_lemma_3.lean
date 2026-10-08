-- Prove2me | solution 1 for AvgLMS.Expect.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:14:54.093991+00:00
-- url     : https://prove2.me/submissions/bb64731d-6c65-46c2-a01d-6f6e8f6ce865

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

open AvgLMS.Expect in
theorem solution :
    ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ n : ℕ, 0 < n → (1 - (1 - u) ^ n) ^ 2 ≤ (n : ℝ) * u := by
  intro u hu0 hu1 n _hn
  have h1 : 0 ≤ 1 - u := by linarith
  have ha0 : 0 ≤ (1 - u) ^ n := pow_nonneg h1 n
  have ha1 : (1 - u) ^ n ≤ 1 := pow_le_one₀ h1 (by linarith)
  have hb : 1 + (n : ℝ) * (-u) ≤ (1 + -u) ^ n :=
    one_add_mul_le_pow (by linarith) n
  have hb' : 1 - (n : ℝ) * u ≤ (1 - u) ^ n := by
    have : (1 + -u) = 1 - u := by ring
    rw [this] at hb; linarith
  nlinarith
