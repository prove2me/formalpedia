-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.moment
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:22.049446+00:00
-- url     : https://prove2.me/submissions/cb01fba0-5db3-4477-b472-6461200eb589

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DetMulDiagonalMulEqSum
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_det_mul_diagonal_mul_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Polynomial Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (A : Matrix (Fin k) n ℂ)
    (hA : A * Aᴴ = 1) (ν : n → ℂ) (m : ℕ) :
    ∑ J ∈ powersetCard k (univ : Finset n),
      (∏ j ∈ J, (1 + X * C (ν j))).coeff m *
        ((Aᴴ * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))).det
    = (det (1 + (X : ℂ[X]) • (A * diagonal ν * Aᴴ).map C)).coeff m := by
  have h := det_mul_diagonal_mul_eq_sum (A.map C) (Aᴴ.map C) (fun j => 1 + X * C (ν j))
  have hd : diagonal (fun j => (1 : ℂ[X]) + X * C (ν j)) = 1 + (X : ℂ[X]) • (diagonal ν).map C := by
    ext a b; by_cases hab : a = b <;> simp [diagonal, one_apply, hab]
  have h1 : A.map C * Aᴴ.map C = 1 := by rw [← Matrix.map_mul, hA]; simp
  have h3 : A.map C * (diagonal ν).map C * Aᴴ.map C = (A * diagonal ν * Aᴴ).map C := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have e : A.map C * diagonal (fun j => 1 + X * C (ν j)) * Aᴴ.map C
      = 1 + (X : ℂ[X]) • (A * diagonal ν * Aᴴ).map C := by
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, Matrix.mul_smul, Matrix.smul_mul, h3]
  rw [e] at h
  rw [h, finsetSum_coeff]
  refine sum_congr rfl fun J _ => ?_
  have hs : (Aᴴ.map C * A.map C).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))
      = ((Aᴴ * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))).map C := by
    rw [← Matrix.map_mul]; rfl
  have hdet : (((Aᴴ * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))).map C).det
      = C ((Aᴴ * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))).det := by
    rw [RingHom.map_det]; rfl
  rw [hs, hdet, coeff_mul_C]
end Formalism.NuclearRankWeightBounds.P
