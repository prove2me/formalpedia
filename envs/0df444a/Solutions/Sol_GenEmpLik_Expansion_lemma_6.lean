-- Prove2me | solution 1 for GenEmpLik.Expansion.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:59:56.055357+00:00
-- url     : https://prove2.me/submissions/8ca32936-2b8b-4c13-b426-38a9b273735a

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_AssumptionA
import Definitions.Def_GenEmpLik_Expansion_huber
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar
import Theorems.Thm_GenEmpLik_Expansion_eq_32
import Theorems.Thm_GenEmpLik_Expansion_lemma_8
import Theorems.Thm_GenEmpLik_Expansion_lemma_9

open VarianceRegularization.Expansion

open GenEmpLik.Expansion in
theorem solution (f : ℝ → EReal) (hA : AssumptionA f) {n : ℕ} (hn : 0 < n) {ρ ε C : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 ≤ C) (hCε : C * ε < 1)
    (hlow : ∀ t : ℝ, -1 ≤ t → ((2 * (1 - C * ε) * huber ε t : ℝ) : EReal) ≤ f (t + 1))
    (hup : ∀ t : ℝ, |t| ≤ ε → f (t + 1) ≤ (((1 + C * ε) * t ^ 2 : ℝ) : EReal))
    (z : Fin n → ℝ)
    (hE : (⨆ i, |z i - empMean z|) / Real.sqrt n ≤
      ε * Real.sqrt (empVar z) * Real.sqrt ((1 - C * ε) / ρ)) :
    empMean z + Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 + C * ε)) ≤
        robustMean f ρ z ∧
      robustMean f ρ z ≤
        empMean z + Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 - C * ε)) := by
  have h32 := eq_32 f hA hn hρ hε hε1 hC hCε hlow hup z
  have hE_plus : (⨆ i, |z i - empMean z|) / Real.sqrt n ≤
      ε * Real.sqrt (empVar z) * Real.sqrt ((1 + C * ε) / ρ) := by
    refine le_trans hE ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hε.le (Real.sqrt_nonneg _))
    refine Real.sqrt_le_sqrt ?_
    exact div_le_div_of_nonneg_right (by nlinarith) hρ.le
  have h8 := lemma_8 hn hρ hε hC z hE_plus
  have h9 := lemma_9 hn hρ hε hC hCε z hE
  refine ⟨?_, ?_⟩
  · linarith [h32.1, h8]
  · linarith [h32.2.1, h32.2.2, h9]
