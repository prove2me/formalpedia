-- Prove2me | solution 1 for DetANN.Thm11.localGuarantee_of_local_ann
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:33:22.432806+00:00
-- url     : https://prove2.me/submissions/713e06ce-6492-4ac8-a6bd-8ab7657000dc

import Mathlib
import Definitions.Def_DetANN_Thm11_LocalProjection
import Theorems.Thm_DetANN_Thm11_annProject_sub_norm_sq

open DetANN DetANN.Thm11

theorem solution {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (q : EuclideanSpace ℝ (Fin (2 ^ k)))
    (r : ∀ v : Fin (2 ^ k), Fin (projectedSet C₀ k P ε v).card)
    (hr : ∀ (v : Fin (2 ^ k)) (a : Fin (projectedSet C₀ k P ε v).card),
      ‖annProject C₀ k P ε v q - localData C₀ k P ε v (r v)‖ ≤
        (1 + ε / 100) * ‖annProject C₀ k P ε v q - localData C₀ k P ε v a‖) :
    LocalGuarantee (annBlocks C₀ k P ε) (annTuples k ε) (paddedSet k P) q
      (fun v => padVec (2 ^ k) (P (localRepIdx C₀ k P ε v (r v)))) (1 + ε / 100) := by
  intro v y hy
  rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
  have h := hr v (localClass C₀ k P ε v i)
  rw [← annProject_localRepIdx C₀ k P ε v (r v), localData_localClass] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  dsimp only
  rw [← annProject_sub_norm_sq, ← annProject_sub_norm_sq, annProject_sub, annProject_sub]
  calc
    ‖annProject C₀ k P ε v q - annProject C₀ k P ε v (padVec (2 ^ k) (P _))‖ ^ 2
        ≤ ((1 + ε / 100) * ‖annProject C₀ k P ε v q -
            annProject C₀ k P ε v (padVec (2 ^ k) (P i))‖) ^ 2 := hs
    _ = (1 + ε / 100) ^ 2 * ‖annProject C₀ k P ε v q -
            annProject C₀ k P ε v (padVec (2 ^ k) (P i))‖ ^ 2 := by ring
