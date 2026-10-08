-- Prove2me | solution 1 for Conway99Formal.CubicOperators.Graph.hasTriangleTightness_of_incidence_square
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T06:45:36.744215+00:00
-- url     : https://prove2.me/submissions/429bde94-45cd-46bf-9483-80dc53feb309

import Definitions.Def_CubicOperators
import Mathlib

namespace Conway99Formal.CubicOperators.Graph
end Conway99Formal.CubicOperators.Graph

set_option autoImplicit false

/-! Algebraic contraction lemmas for the graph-owned triangle cubic. The
incidence identities in the hypotheses are the explicit graph bridge. -/

namespace Conway99Formal.CubicOperators

open Finset

variable {T I : Type*} [Fintype T] [Fintype I]





























































end Conway99Formal.CubicOperators

namespace Conway99Formal.CubicOperators.Graph

open Finset



variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]





















theorem triangleVector_eq_matrix (Pi : Matrix Coord V ℝ)
    (T : Triangle G) (i : Coord) :
    triangleVector G Pi T i = (Pi * realIncidenceMatrix G) i T / 3 := by
  have hfilt : (Finset.univ.filter fun u : V => u ∈ T.1) = T.1 := by
    ext u
    simp
  simp only [triangleVector, Matrix.mul_apply, realIncidenceMatrix]
  rw [← hfilt, Finset.sum_filter]
  simp




























































end Conway99Formal.CubicOperators.Graph

set_option autoImplicit false

/-! Algebraic contraction lemmas for the graph-owned triangle cubic. The
incidence identities in the hypotheses are the explicit graph bridge. -/

open Conway99Formal.CubicOperators

open Finset

variable {T I : Type*} [Fintype T] [Fintype I]






























































open Conway99Formal.CubicOperators.Graph

open Finset



variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Conway99Formal.CubicOperators.Graph in
theorem solution (Pi : Matrix Coord V ℝ)
    (hf : IsPointFrame G Pi)
    (hinc : realIncidenceMatrix G * (realIncidenceMatrix G).transpose =
      7 • (1 : Matrix V V ℝ) + G.adjMatrix ℝ) :
    HasTriangleTightness G Pi := by
  let N := realIncidenceMatrix G
  have hPN : Pi * (N * N.transpose) = 3 • Pi := by
    rw [hinc, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hf.adjacency]
    ext i u
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, nsmul_eq_mul]
    ring
  have hW : (Pi * N) * (Pi * N).transpose =
      189 • (1 : Matrix Coord Coord ℝ) := by
    rw [Matrix.transpose_mul]
    calc
      (Pi * N) * (N.transpose * Pi.transpose) =
          (Pi * (N * N.transpose)) * Pi.transpose := by
        simp only [Matrix.mul_assoc]
      _ = (3 • Pi) * Pi.transpose := by rw [hPN]
      _ = 3 • (Pi * Pi.transpose) := by rw [Matrix.smul_mul]
      _ = 3 • (63 • (1 : Matrix Coord Coord ℝ)) := by rw [hf.tight]
      _ = 189 • (1 : Matrix Coord Coord ℝ) := by
        simp only [smul_smul]
        norm_num
  intro i j
  have hij : (∑ T : Triangle G, (Pi * N) i T * (Pi * N) j T) =
      189 • (if i = j then (1 : ℝ) else 0) := by
    have hentry := congrArg (fun M : Matrix Coord Coord ℝ => M i j) hW
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply] using hentry
  calc
    (∑ T : Triangle G,
      triangleVector G Pi T i * triangleVector G Pi T j) =
        (∑ T : Triangle G, (Pi * N) i T * (Pi * N) j T) / 9 := by
      calc
        (∑ T : Triangle G,
          triangleVector G Pi T i * triangleVector G Pi T j) =
            ∑ T : Triangle G, ((Pi * N) i T * (Pi * N) j T) / 9 := by
          apply Finset.sum_congr rfl
          intro T _
          change triangleVector G Pi T i * triangleVector G Pi T j =
            ((Pi * realIncidenceMatrix G) i T *
              (Pi * realIncidenceMatrix G) j T) / 9
          rw [triangleVector_eq_matrix, triangleVector_eq_matrix]
          ring
        _ = (∑ T : Triangle G, (Pi * N) i T * (Pi * N) j T) / 9 := by
          rw [Finset.sum_div]
    _ = 21 * (if i = j then (1 : ℝ) else 0) := by
      rw [hij]
      simp only [nsmul_eq_mul]
      ring
