-- Prove2me | solution 1 for BicliqueSDP.Chain.proposition_1_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:22:33.291361+00:00
-- url     : https://prove2.me/submissions/78c1a6e1-c275-4a87-9506-03f1f3e88781

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model
import Theorems.Thm_BicliqueSDP_Chain_lemma_1_1
import Theorems.Thm_BicliqueSDP_Chain_sqrt_g_le_h1
import Theorems.Thm_BicliqueSDP_Chain_h1_le_sqrt_g1
import Theorems.Thm_BicliqueSDP_Chain_h1_le_alpha
import Theorems.Thm_BicliqueSDP_Chain_g1_le_alpha_mul_h1

set_option autoImplicit false

open BicliqueSDP.Chain

/-- Proposition 1.2 reduced to the five existing milestones from the paper. -/
theorem solution {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    h E ≤ (1 / 2) * Real.sqrt (g E) ∧ (1 / 2) * Real.sqrt (g E) ≤ h1 E ∧
      h1 E ≤ (1 / 2) * Real.sqrt (g1 E) ∧ (1 / 2) * Real.sqrt (g1 E) ≤ (1 / 4) * alpha E := by
  have halpha : 0 ≤ alpha E := by
    simpa [alpha] using
      (Finset.le_sup'
        (fun p : Finset V1 × Finset V2 => (p.1.card : ℝ) + p.2.card)
        (empty_mem_pairs E))
  have hg1 : g1 E ≤ (alpha E / 2) ^ 2 := by
    calc
      g1 E ≤ alpha E * h1 E := g1_le_alpha_mul_h1 E
      _ ≤ alpha E * ((1 / 4) * alpha E) :=
        mul_le_mul_of_nonneg_left (h1_le_alpha E) halpha
      _ = (alpha E / 2) ^ 2 := by ring
  have hsqrt : Real.sqrt (g1 E) ≤ alpha E / 2 := by
    calc
      Real.sqrt (g1 E) ≤ Real.sqrt ((alpha E / 2) ^ 2) := Real.sqrt_le_sqrt hg1
      _ = alpha E / 2 := Real.sqrt_sq (by positivity)
  exact ⟨(lemma_1_1 E).1.2.2.2.1, sqrt_g_le_h1 E, h1_le_sqrt_g1 E, by linarith⟩
