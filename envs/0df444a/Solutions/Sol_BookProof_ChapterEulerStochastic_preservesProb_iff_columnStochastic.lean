-- Prove2me | solution 1 for BookProof.ChapterEulerStochastic.preservesProb_iff_columnStochastic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:53:41.470427+00:00
-- url     : https://prove2.me/submissions/df0f2e08-9668-46c7-b5c3-20d813830dde

-- Generated from ChapterEulerStochastic.lean — solution of BookProof.ChapterEulerStochastic.preservesProb_iff_columnStochastic
import Mathlib
import Definitions.Def_ChapterEulerStochastic
open BookProof.ChapterEulerStochastic



open scoped Matrix BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 2) (Fin 2) ℝ) :
    PreservesProb M ↔
      (IsProbVec (fun i => M i 0) ∧ IsProbVec (fun i => M i 1)) := by

    refine ⟨?_, fun h => ?_⟩
    · intro hM
      constructor
      · have := hM (fun i => if i = 0 then 1 else 0)
        simp only [IsProbVec, Fin.isValue, Fin.forall_fin_two, ↓reduceIte, zero_le_one, one_ne_zero,
            le_refl, and_self, add_zero, Matrix.mulVec, Matrix.vec2_dotProduct, mul_one, mul_zero,
                forall_const] at this ⊢
        exact this
      · have := hM (fun i => if i = 0 then 0 else 1)
        simp only [IsProbVec, Fin.isValue, Fin.forall_fin_two, ↓reduceIte, le_refl, one_ne_zero,
            zero_le_one, and_self, zero_add, Matrix.mulVec, Matrix.vec2_dotProduct, mul_zero,
                mul_one, forall_const] at this ⊢
        exact this
    · intro v hv
      rcases hv with ⟨hv_nonneg, hvsum⟩
      have hv0 : 0 ≤ v 0 := hv_nonneg 0
      have hv1 : 0 ≤ v 1 := hv_nonneg 1
      have h0 := h.1
      have h1 := h.2
      simp only [IsProbVec, Fin.isValue, Fin.forall_fin_two] at h0 h1
      rcases h0 with ⟨⟨hM00, hM10⟩, hMsum0⟩
      rcases h1 with ⟨⟨hM01, hM11⟩, hMsum1⟩
      simp only [IsProbVec, Matrix.mulVec, Matrix.vec2_dotProduct, Fin.isValue, Fin.forall_fin_two]
      have hsum : (M 0 0 * v 0 + M 0 1 * v 1) + (M 1 0 * v 0 + M 1 1 * v 1) = 1 := by
        nlinarith
      have hpos0 : 0 ≤ M 0 0 * v 0 + M 0 1 * v 1 := by
        nlinarith
      have hpos1 : 0 ≤ M 1 0 * v 0 + M 1 1 * v 1 := by
        nlinarith
      exact ⟨⟨hpos0, hpos1⟩, hsum⟩
