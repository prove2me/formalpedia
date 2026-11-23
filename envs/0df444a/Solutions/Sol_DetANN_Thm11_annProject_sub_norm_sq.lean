-- Prove2me | solution 1 for DetANN.Thm11.annProject_sub_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:29:32.613596+00:00
-- url     : https://prove2.me/submissions/c2d3cdf5-3282-4ad8-9bda-605af7ddad07

import Mathlib
import Definitions.Def_DetANN_Thm11_LocalProjection

open DetANN DetANN.Thm11

theorem solution {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k))
    (z w : EuclideanSpace ℝ (Fin (2 ^ k))) :
    ‖annProject C₀ k P ε v (z - w)‖ ^ 2 =
      superNormSq (annBlocks C₀ k P ε) (annTuples k ε) v (z - w) := by
  simp only [EuclideanSpace.norm_sq_eq, superNormSq]
  change (∑ c : Fin (16 ^ walkLen ε * annReps C₀ k P ε),
      ‖annBlocks C₀ k P ε
        (annTuples k ε v (occEquiv ε (finProdFinEquiv.symm c).1)) (z - w)
        (finProdFinEquiv.symm c).2‖ ^ 2) = _
  calc
    _ = ∑ p : Fin (16 ^ walkLen ε) × Fin (annReps C₀ k P ε),
        ‖annBlocks C₀ k P ε (annTuples k ε v (occEquiv ε p.1)) (z - w) p.2‖ ^ 2 :=
      Equiv.sum_comp finProdFinEquiv.symm _
    _ = ∑ o : Fin (16 ^ walkLen ε), ∑ r : Fin (annReps C₀ k P ε),
        ‖annBlocks C₀ k P ε (annTuples k ε v (occEquiv ε o)) (z - w) r‖ ^ 2 :=
      Fintype.sum_prod_type _
    _ = _ := Equiv.sum_comp (occEquiv ε)
      (fun o : WalkOcc ε => ∑ r : Fin (annReps C₀ k P ε),
        ‖annBlocks C₀ k P ε (annTuples k ε v o) (z - w) r‖ ^ 2)
