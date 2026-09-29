-- Prove2me | solution 1 for Freiman.cert_weighted_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:37:44.237458+00:00
-- url     : https://prove2.me/submissions/ad6974f4-4139-4696-97d5-a206eb7185a7

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
    ∀ v w : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, 0 < v i j) → (∀ i j : Fin 3, 0 ≤ w i j) → (∑ i : Fin 3, ∑ j : Fin 3, w i j)=1 → 0 < ∑ i : Fin 3, ∑ j : Fin 3, v i j*w i j := by
  intro v w hv hw hsum
  have hex : ∃ i j, 0 < w i j := by
    by_contra! h
    have hz : ∀ i j, w i j = 0 := fun i j => le_antisymm (h i j) (hw i j)
    simp only [hz, Finset.sum_const_zero] at hsum
    norm_num at hsum
  rcases hex with ⟨i,j,hij⟩
  apply Finset.sum_pos'
  · intro i _
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hv i j).le (hw i j))
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hv i j).le (hw i j)
    · exact ⟨j, Finset.mem_univ j, mul_pos (hv i j) hij⟩


#print axioms solution
