-- Prove2me | solution 1 for CompDesign.thm_4_1_terminal_is_pne
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:23:24.228202+00:00
-- url     : https://prove2.me/submissions/8519d4a6-3936-4e8a-b411-4480eb7ac366

import Mathlib
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesign_IsStrictImprovement

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) (h : ∀ S' : Finset (Fin n), ¬ CompDesign.IsStrictImprovement v B c S S') :
    IsPNE v B c S := by
  constructor
  · intro i hi
    by_contra hlt
    push Not at hlt
    apply h (S.erase i)
    refine ⟨i, by simp [CompDesign.switch, hi], ?_⟩
    simp only [CompDesign.util, hi, Finset.notMem_erase i S, if_true, if_false]
    linarith
  · intro i hi
    by_contra hlt
    push Not at hlt
    apply h (insert i S)
    refine ⟨i, by simp [CompDesign.switch, hi], ?_⟩
    simp only [CompDesign.util, hi, Finset.mem_insert_self, if_true, if_false]
    linarith
