-- Prove2me | solution 1 for ConvexOptAlg.GoemansWilliamson.sdp_relaxation_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:39:54.062178+00:00
-- url     : https://prove2.me/submissions/ca6b31f5-45e7-4fe5-b0dd-5c73c10d457c

import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs

open ConvexOptAlg.GoemansWilliamson Matrix in
theorem gw8999_frob_vecMulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    frobInner M (vecMulVec x x) = x ⬝ᵥ M *ᵥ x := by
  unfold frobInner
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

open ConvexOptAlg.GoemansWilliamson Matrix in
theorem gw8999_feasible {n : ℕ} (b : Fin n → Bool) :
    IsSDPFeasible (vecMulVec (fun i => signOfBool (b i)) (fun i => signOfBool (b i))) := by
  refine ⟨?_, ?_⟩
  · have h := Matrix.posSemidef_vecMulVec_self_star (fun i => signOfBool (b i))
    simpa using h
  · intro i
    rw [Matrix.vecMulVec_apply]
    unfold signOfBool
    split_ifs <;> norm_num

open Matrix in
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ConvexOptAlg.GoemansWilliamson.hypercubeMax (ConvexOptAlg.GoemansWilliamson.laplacian A) =
        Finset.univ.sup' Finset.univ_nonempty (fun b : Fin n → Bool =>
          ConvexOptAlg.GoemansWilliamson.frobInner (ConvexOptAlg.GoemansWilliamson.laplacian A)
            (vecMulVec (fun i => ConvexOptAlg.GoemansWilliamson.signOfBool (b i))
              (fun i => ConvexOptAlg.GoemansWilliamson.signOfBool (b i)))) ∧
      (∀ b : Fin n → Bool,
        ConvexOptAlg.GoemansWilliamson.IsSDPFeasible
          (vecMulVec (fun i => ConvexOptAlg.GoemansWilliamson.signOfBool (b i))
            (fun i => ConvexOptAlg.GoemansWilliamson.signOfBool (b i)))) ∧
      ∀ Sig : Matrix (Fin n) (Fin n) ℝ,
        ConvexOptAlg.GoemansWilliamson.IsSDPRelaxationOptimum
          (ConvexOptAlg.GoemansWilliamson.laplacian A) Sig →
        ConvexOptAlg.GoemansWilliamson.hypercubeMax (ConvexOptAlg.GoemansWilliamson.laplacian A) ≤
          ConvexOptAlg.GoemansWilliamson.frobInner (ConvexOptAlg.GoemansWilliamson.laplacian A) Sig := by
  have hEq : ConvexOptAlg.GoemansWilliamson.hypercubeMax (ConvexOptAlg.GoemansWilliamson.laplacian A) =
        Finset.univ.sup' Finset.univ_nonempty (fun b : Fin n → Bool =>
          ConvexOptAlg.GoemansWilliamson.frobInner (ConvexOptAlg.GoemansWilliamson.laplacian A)
            (vecMulVec (fun i => ConvexOptAlg.GoemansWilliamson.signOfBool (b i))
              (fun i => ConvexOptAlg.GoemansWilliamson.signOfBool (b i)))) := by
    unfold ConvexOptAlg.GoemansWilliamson.hypercubeMax
    congr 1
    funext b
    rw [gw8999_frob_vecMulVec]
  refine ⟨hEq, gw8999_feasible, ?_⟩
  intro Sig hSig
  rw [hEq]
  refine Finset.sup'_le _ _ (fun b _ => ?_)
  exact hSig.2 _ (gw8999_feasible b)
