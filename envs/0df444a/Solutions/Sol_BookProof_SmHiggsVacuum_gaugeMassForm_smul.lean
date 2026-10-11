-- Prove2me | solution 1 for BookProof.SmHiggsVacuum.gaugeMassForm_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:20:59.753778+00:00
-- url     : https://prove2.me/submissions/dbe98211-072f-461c-86b4-da89a37dcb9d

-- Generated from ChapterSmHiggsVacuum.lean — solution of BookProof.SmHiggsVacuum.gaugeMassForm_smul
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
open BookProof.SmHiggsVacuum




open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (X : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ) (u : Fin 4 → ℝ) (c : ℝ) :
    gaugeMassForm (fun i => c • X i) u = c ^ 2 * gaugeMassForm X u := by

  have hsm : ∀ (i : Fin 3) (a : Fin 4), ((c • X i).mulVec u) a = c * ((X i).mulVec u a) := by
    intro i a
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hrow : ∀ i : Fin 3, ∑ a : Fin 4, (((c • X i).mulVec u) a) ^ 2
      = c ^ 2 * ∑ a : Fin 4, ((X i).mulVec u a) ^ 2 := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [hsm i a]; ring
  simp only [gaugeMassForm]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hrow i, ← Finset.mul_sum]
  ring
