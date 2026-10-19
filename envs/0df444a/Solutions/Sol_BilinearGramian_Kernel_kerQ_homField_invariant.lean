-- Prove2me | solution 1 for BilinearGramian.Kernel.kerQ_homField_invariant
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-18T09:16:39.168946+00:00
-- url     : https://prove2.me/submissions/939a5e08-6733-4d64-8c1a-e7256bccb5e1

import Mathlib
import Definitions.Def_BilinearGramian_Kernel_GramianEquations
import Definitions.Def_BilinearGramian_Kernel_System

open Matrix
open BilinearGramian.Kernel

private theorem kerQ_subset_aux {n m p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) (hQeq : ObsGramianEq A N C Q) :
    (∀ j : Fin m,
      (LinearMap.ker (Matrix.toLin' Q)).map (Matrix.toLin' (N j)) ≤
        LinearMap.ker (Matrix.toLin' Q)) ∧
    LinearMap.ker (Matrix.toLin' Q) ≤ LinearMap.ker (Matrix.toLin' C) ∧
    (LinearMap.ker (Matrix.toLin' Q)).map (Matrix.toLin' A) ≤
      LinearMap.ker (Matrix.toLin' Q) := by
  have hsym : Qᵀ = Q := by simpa using hQ.isHermitian.eq
  have core (z : Fin n → ℝ) (hz : Q *ᵥ z = 0) :
      (∀ j, Q *ᵥ (N j *ᵥ z) = 0) ∧ C *ᵥ z = 0 ∧ Q *ᵥ (A *ᵥ z) = 0 := by
    have hrow : z ᵥ* Q = 0 := by
      rw [← hsym, vecMul_transpose, hz]
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => z ⬝ᵥ (M *ᵥ z)) hQeq
    have he' : (∑ j, (N j *ᵥ z) ⬝ᵥ (Q *ᵥ (N j *ᵥ z))) =
        -((C *ᵥ z) ⬝ᵥ (C *ᵥ z)) := by
      simpa only [add_mulVec, sum_mulVec, neg_mulVec, ← mulVec_mulVec,
        dotProduct_add, dotProduct_sum, dotProduct_neg, dotProduct_transpose_mulVec,
        hz, mulVec_zero, dotProduct_zero, zero_add, dotProduct_mulVec z Q,
        hrow, zero_dotProduct, dotProduct_comm (Q *ᵥ _) _] using he
    have hn (j : Fin m) : 0 ≤ (N j *ᵥ z) ⬝ᵥ (Q *ᵥ (N j *ᵥ z)) := by
      simpa using hQ.dotProduct_mulVec_nonneg (N j *ᵥ z)
    have hc : 0 ≤ (C *ᵥ z) ⬝ᵥ (C *ᵥ z) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hs : 0 ≤ ∑ j, (N j *ᵥ z) ⬝ᵥ (Q *ᵥ (N j *ᵥ z)) :=
      Finset.sum_nonneg fun j _ => hn j
    have hc0 : (C *ᵥ z) ⬝ᵥ (C *ᵥ z) = 0 := by linarith
    have hn0 (j : Fin m) : Q *ᵥ (N j *ᵥ z) = 0 := by
      apply (hQ.dotProduct_mulVec_zero_iff _).mp
      simp only [star_trivial]
      have hj := Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ j)
      linarith [hn j]
    have hcvec : C *ᵥ z = 0 := (dotProduct_self_eq_zero.mp hc0)
    refine ⟨hn0, hcvec, ?_⟩
    have hv := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M *ᵥ z) hQeq
    simpa only [add_mulVec, sum_mulVec, neg_mulVec, ← mulVec_mulVec,
      hz, hn0, hcvec, mulVec_zero, Finset.sum_const_zero, zero_add, add_zero,
      neg_zero] using hv
  refine ⟨?_, ?_, ?_⟩
  · intro j y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (core z hz).1 j
  · intro z hz
    exact (core z hz).2.1
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (core z hz).2.2


theorem solution {n m p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) (hQeq : ObsGramianEq A N C Q)
    (z : Fin n → ℝ) (hz : z ∈ LinearMap.ker (Matrix.toLin' Q)) (w : Fin m → ℝ) :
    homField A N z w ∈ LinearMap.ker (Matrix.toLin' Q) := by
  obtain ⟨hN, _, hA⟩ := kerQ_subset_aux A N C Q hQ hQeq
  apply Submodule.add_mem
  · exact hA (Submodule.mem_map_of_mem hz)
  · apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ (w j) (hN j (Submodule.mem_map_of_mem hz))

#print axioms solution
