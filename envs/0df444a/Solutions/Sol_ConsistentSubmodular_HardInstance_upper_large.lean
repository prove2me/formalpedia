-- Prove2me | solution 1 for ConsistentSubmodular.HardInstance.upper_large
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:13.741352+00:00
-- url     : https://prove2.me/submissions/7c90efcf-7184-4a9a-b812-e72ae6e334e7

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

open scoped BigOperators
open Finset
open ConsistentSubmodular

theorem solution {k : ℕ} {ε ρ : ℝ} (hk : 0 < k) (hρ : 1 ≤ ρ) :
    ∃ (n u : ℕ) (cover : Fin n → Finset (Fin u)),
      ∀ μ : RandomTrajectory n, μ.Feasible k ⌊ε * k⌋₊ →
        ∃ (t : Fin (n + 1)) (A : Finset (Fin n)),
          A ⊆ arrivedPrefix n t.val ∧ A.card ≤ k ∧ 0 < coverageValue cover A ∧
          μ.expectation (coverageValue cover) t ≤ ρ * coverageValue cover A := by
  refine ⟨1, 1, fun _ => univ, fun μ _ => ⟨Fin.last 1, univ, ?_, ?_, ?_, ?_⟩⟩
  · intro e _
    exact mem_filter.mpr ⟨mem_univ _, e.isLt⟩
  · simpa using (show 1 ≤ k from hk)
  · simp [coverageValue]
  · have hcov : ∀ T : Finset (Fin 1), coverageValue (fun _ : Fin 1 => (univ : Finset (Fin 1))) T ≤ 1 :=
      fun T => by
        unfold coverageValue
        exact_mod_cast (card_le_univ _).trans (by simp)
    have hall : coverageValue (fun _ : Fin 1 => (univ : Finset (Fin 1))) univ = 1 := by
      simp [coverageValue]
    rw [hall, mul_one]
    calc μ.expectation (coverageValue fun _ => univ) (Fin.last 1)
        ≤ ∑ S, μ.prob S * 1 := Finset.sum_le_sum fun S _ =>
          mul_le_mul_of_nonneg_left (hcov _) (μ.prob_nonneg S)
      _ = 1 := by simp [μ.prob_sum]
      _ ≤ ρ := hρ

end
