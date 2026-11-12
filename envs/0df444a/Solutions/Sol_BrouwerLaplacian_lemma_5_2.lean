-- Prove2me | solution 1 for BrouwerLaplacian.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:14:09.555237+00:00
-- url     : https://prove2.me/submissions/22dd0d19-8752-4606-9af0-9940cc4911fb

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj

section
namespace BrouwerLaplacian.Dev.Common

open Matrix

theorem trace_eq_rank {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P * P = P) (hk : P.rank = k) :
    P.trace = k := by
  have hproj : LinearMap.IsProj (LinearMap.range (Matrix.toLin' P)) (Matrix.toLin' P) := by
    have : IsIdempotentElem (Matrix.toLin' P) := by
      show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
    exact (LinearMap.isProj_range_iff_isIdempotentElem _).2 this
  have h := hproj.trace
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin n)), LinearMap.toMatrix_eq_toMatrix'] at h
  rw [LinearMap.toMatrix'_toLin'] at h
  rw [h]
  have : P.rank = Module.finrank ℝ (LinearMap.range (Matrix.toLin' P)) := by
    rw [Matrix.rank]; rfl
  rw [← this, hk]

end BrouwerLaplacian.Dev.Common
end

section
namespace BrouwerLaplacian.Dev.L52

open Finset Matrix

theorem symm_of {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : BrouwerLaplacian.IsOrthProj P k)
    (i j : Fin n) : P j i = P i j := by
  have := hP.1.apply i j
  simpa using this

theorem rowsum {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP1 : P *ᵥ (fun _ => 1) = 0) (i : Fin n) :
    ∑ j, P i j = 0 := by
  have := congrFun hP1 i
  simpa [Matrix.mulVec, dotProduct] using this

theorem sumsq {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : BrouwerLaplacian.IsOrthProj P k) :
    ∑ i, ∑ j, P i j ^ 2 = k := by
  have h1 : P.trace = k := Common.trace_eq_rank P hP.2.1 hP.2.2
  have h2 : (P * P).trace = ∑ i, ∑ j, P i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [symm_of hP j i]; ring
  rw [← h2, hP.2.1, h1]

theorem full_sum {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : BrouwerLaplacian.IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    ∑ i, ∑ j, ((P i i + P j j - 2 * P i j) ^ 2 - (P i i - P j j) ^ 2)
      = 4 * (k : ℝ) * ((k : ℝ) + 1) := by
  have htr : ∑ i, P i i = k := Common.trace_eq_rank P hP.2.1 hP.2.2
  have hsq := sumsq hP
  have hrow := rowsum hP1
  have hmid : ∑ i, ∑ j, (P i i + P j j) * P i j = 0 := by
    have e1 : ∑ i, ∑ j, P i i * P i j = 0 := by
      refine sum_eq_zero fun i _ => ?_
      rw [← mul_sum, hrow i, mul_zero]
    have e2 : ∑ i, ∑ j, P j j * P i j = 0 := by
      rw [sum_comm]
      refine sum_eq_zero fun j _ => ?_
      rw [← mul_sum]
      have : ∑ i, P i j = 0 := by
        simp_rw [symm_of hP j]; exact hrow j
      rw [this, mul_zero]
    simp_rw [add_mul, sum_add_distrib]
    rw [e1, e2, add_zero]
  have expand : ∀ i j, ((P i i + P j j - 2 * P i j) ^ 2 - (P i i - P j j) ^ 2)
      = 4 * (P i i * P j j) - 4 * ((P i i + P j j) * P i j) + 4 * P i j ^ 2 := by
    intro i j; ring
  simp_rw [expand, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hmid, hsq, htr, ← sum_mul, htr]; ring

theorem main {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : BrouwerLaplacian.IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    (1 / 4 : ℝ) * ∑ i, ∑ j with i ≠ j,
        ((P i i + P j j - 2 * P i j) ^ 2 - (P i i - P j j) ^ 2)
      = (k : ℝ) * ((k : ℝ) + 1) := by
  have h := full_sum hP hP1
  have : ∀ i, ∑ j with i ≠ j, ((P i i + P j j - 2 * P i j) ^ 2 - (P i i - P j j) ^ 2)
      = ∑ j, ((P i i + P j j - 2 * P i j) ^ 2 - (P i i - P j j) ^ 2) := by
    intro i
    rw [sum_filter]
    refine sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp [hij]
  simp_rw [this, h]; ring

end BrouwerLaplacian.Dev.L52

namespace BrouwerLaplacian
open Finset Matrix
theorem chk_lemma_5_2 {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    (1 / 4 : ℝ) * ∑ i, ∑ j with i ≠ j,
        ((P i i + P j j - 2 * P i j) ^ 2 - (P i i - P j j) ^ 2)
      = (k : ℝ) * ((k : ℝ) + 1) := Dev.L52.main P hP hP1
end BrouwerLaplacian
end

theorem solution : type_of% @BrouwerLaplacian.chk_lemma_5_2 := @BrouwerLaplacian.chk_lemma_5_2
