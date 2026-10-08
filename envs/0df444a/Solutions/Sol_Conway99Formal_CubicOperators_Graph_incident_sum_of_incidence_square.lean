-- Prove2me | solution 1 for Conway99Formal.CubicOperators.Graph.incident_sum_of_incidence_square
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T06:45:37.627976+00:00
-- url     : https://prove2.me/submissions/5729e536-c1ec-48e0-baf0-2b4e6f8619c3

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
      7 • (1 : Matrix V V ℝ) + G.adjMatrix ℝ)
    (u : V) (i : Coord) :
    (∑ T : Triangle G, incidence G u T * triangleVector G Pi T i) =
      pointColumn Pi u i := by
  have hsum : (∑ T : Triangle G,
        incidence G u T * triangleVector G Pi T i) =
      ((Pi * realIncidenceMatrix G) * (realIncidenceMatrix G).transpose) i u / 3 := by
    calc
      (∑ T : Triangle G, incidence G u T * triangleVector G Pi T i) =
          (∑ T : Triangle G, incidence G u T *
            (Pi * realIncidenceMatrix G) i T) / 3 := by
        calc
          (∑ T : Triangle G, incidence G u T * triangleVector G Pi T i) =
              ∑ T : Triangle G, (incidence G u T *
                (Pi * realIncidenceMatrix G) i T) / 3 := by
            apply Finset.sum_congr rfl
            intro T _
            rw [triangleVector_eq_matrix]
            ring
          _ = (∑ T : Triangle G, incidence G u T *
                (Pi * realIncidenceMatrix G) i T) / 3 := by
            rw [Finset.sum_div]
      _ = ((Pi * realIncidenceMatrix G) * (realIncidenceMatrix G).transpose) i u / 3 := by
        rw [Matrix.mul_apply]
        apply congrArg (fun x : ℝ => x / 3)
        apply Finset.sum_congr rfl
        intro T _
        simp only [Matrix.transpose_apply, realIncidenceMatrix, incidence]
        ring
  have hadj := congrArg (fun M : Matrix Coord V ℝ => M i u) hf.adjacency
  simp only [Matrix.neg_apply, Matrix.smul_apply, nsmul_eq_mul] at hadj
  calc
    (∑ T : Triangle G, incidence G u T * triangleVector G Pi T i) =
        ((Pi * realIncidenceMatrix G) * (realIncidenceMatrix G).transpose) i u / 3 :=
      hsum
    _ = (Pi * (realIncidenceMatrix G * (realIncidenceMatrix G).transpose)) i u / 3 := by
      rw [Matrix.mul_assoc]
    _ = ((Pi * (7 • (1 : Matrix V V ℝ) + G.adjMatrix ℝ)) : Matrix Coord V ℝ) i u / 3 := by
      rw [hinc]
    _ = pointColumn Pi u i := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
        Matrix.add_apply, Matrix.smul_apply, pointColumn]
      rw [hadj]
      simp only [nsmul_eq_mul]
      ring
