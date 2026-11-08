-- Prove2me | solution 1 for DistortedCondExp.q_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:40:51.808884+00:00
-- url     : https://prove2.me/submissions/3c9091b0-1b93-42f2-b27b-b331d5202199

import Mathlib
import Definitions.Def_DistortedCondExp_Distortion
import Definitions.Def_DistortedCondExp_Tree
import Definitions.Def_DistortedCondExp_Dynamic

open MeasureTheory Set

open DistortedCondExp in
theorem solution (N : ℕ) (x p : ℕ → ℕ → ℝ) (φ : ℕ → ℝ → ℝ)
    (htree : IsBinomialTree N x p) (hφ : ∀ n, 1 ≤ n → n ≤ N → IsDistortion (φ n))
    (h314 : Cond314 N x p φ) :
    ∀ i j, j ≤ i → i < N → 0 < qPlus N x p φ i j ∧ qPlus N x p φ i j < 1 := by
  intro i j hj hi
  obtain ⟨h1, h2⟩ := h314 i j hj hi
  unfold qPlus
  have hden : 0 < phiExt φ i (G N x p i j) - phiExt φ i (G N x p i (j + 1)) := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · rw [div_lt_one hden]; linarith
