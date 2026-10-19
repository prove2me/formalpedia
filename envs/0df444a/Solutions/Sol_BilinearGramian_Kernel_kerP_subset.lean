-- Prove2me | solution 1 for BilinearGramian.Kernel.kerP_subset
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-18T09:13:15.096085+00:00
-- url     : https://prove2.me/submissions/26c0e1c5-fdce-46af-b854-278343b5c71c

import Mathlib
import Definitions.Def_BilinearGramian_Kernel_GramianEquations

open Matrix BilinearGramian.Kernel

private theorem kernel_terms {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (hPeq : ReachGramianEq A N B P)
    (v : Fin n → ℝ) (hv : P *ᵥ v = 0) :
    (∀ j, P *ᵥ ((N j)ᵀ *ᵥ v) = 0) ∧ Bᵀ *ᵥ v = 0 := by
  have hsym : Pᵀ = P := by simpa using hP.isHermitian.eq
  have hleft : v ᵥ* P = 0 := by rw [← mulVec_transpose, hsym, hv]
  have he := congrArg (fun M => v ⬝ᵥ (M *ᵥ v)) hPeq
  change v ⬝ᵥ ((A * P + P * Aᵀ + ∑ j, N j * P * (N j)ᵀ) *ᵥ v) =
    v ⬝ᵥ (-(B * Bᵀ) *ᵥ v) at he
  simp only [add_mulVec, ← mulVec_mulVec, dotProduct_add, hv, mulVec_zero,
    zero_add, dotProduct_mulVec v P, hleft, zero_dotProduct,
    neg_mulVec, dotProduct_neg] at he
  have hn (j : Fin m) : 0 ≤ ((N j)ᵀ *ᵥ v) ⬝ᵥ (P *ᵥ ((N j)ᵀ *ᵥ v)) := by
    simpa using hP.dotProduct_mulVec_nonneg ((N j)ᵀ *ᵥ v)
  have hsum : (∑ j, ((N j)ᵀ *ᵥ v) ⬝ᵥ (P *ᵥ ((N j)ᵀ *ᵥ v))) =
      -((Bᵀ *ᵥ v) ⬝ᵥ (Bᵀ *ᵥ v)) := by
    simpa only [sum_mulVec, dotProduct_sum, ← mulVec_mulVec,
      dotProduct_mulVec v, ← mulVec_transpose] using he
  have hbnon : 0 ≤ (Bᵀ *ᵥ v) ⬝ᵥ (Bᵀ *ᵥ v) := by
    simpa using dotProduct_star_self_nonneg (Bᵀ *ᵥ v)
  have hsnon := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hn j)
  have hbzero : (Bᵀ *ᵥ v) ⬝ᵥ (Bᵀ *ᵥ v) = 0 := by linarith
  have hszero : (∑ j, ((N j)ᵀ *ᵥ v) ⬝ᵥ (P *ᵥ ((N j)ᵀ *ᵥ v))) = 0 := by linarith
  refine ⟨fun j => ?_, dotProduct_self_eq_zero.mp hbzero⟩
  apply (hP.dotProduct_mulVec_zero_iff _).mp
  simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => hn j)).mp hszero j (Finset.mem_univ j)

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (hPeq : ReachGramianEq A N B P) :
    (∀ j : Fin m,
      (LinearMap.ker (Matrix.toLin' P)).map (Matrix.toLin' (N j)ᵀ) ≤
        LinearMap.ker (Matrix.toLin' P)) ∧
    LinearMap.ker (Matrix.toLin' P) ≤ LinearMap.ker (Matrix.toLin' Bᵀ) := by
  constructor
  · intro j y hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact (kernel_terms A N B P hP hPeq v hv).1 j
  · intro v hv
    exact (kernel_terms A N B P hP hPeq v hv).2

#print axioms solution
