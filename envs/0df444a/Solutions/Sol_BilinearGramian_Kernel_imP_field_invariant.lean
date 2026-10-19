-- Prove2me | solution 1 for BilinearGramian.Kernel.imP_field_invariant
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-18T09:19:19.97557+00:00
-- url     : https://prove2.me/submissions/4b6ecf76-d2ad-4628-9eb1-dbb4a21953d5

import Mathlib
import Definitions.Def_BilinearGramian_Kernel_GramianEquations
import Definitions.Def_BilinearGramian_Kernel_System

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

private theorem kernel_A {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (hPeq : ReachGramianEq A N B P)
    (v : Fin n → ℝ) (hv : P *ᵥ v = 0) : P *ᵥ (Aᵀ *ᵥ v) = 0 := by
  obtain ⟨hn, hb⟩ := kernel_terms A N B P hP hPeq v hv
  have he := congrArg (fun M => M *ᵥ v) hPeq
  change (A * P + P * Aᵀ + ∑ j, N j * P * (N j)ᵀ) *ᵥ v =
    -(B * Bᵀ) *ᵥ v at he
  simpa only [add_mulVec, sum_mulVec, ← mulVec_mulVec, hv, hn, hb,
    mulVec_zero, Finset.sum_const_zero, zero_add, add_zero, neg_mulVec, neg_zero] using he

private theorem range_of_annihilates_kernel {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hsym : Pᵀ = P) (y : Fin n → ℝ)
    (hy : ∀ v, P *ᵥ v = 0 → v ⬝ᵥ y = 0) :
    y ∈ LinearMap.range (Matrix.toLin' P) := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  let v : Fin n → ℝ := fun i => φ (fun j => if i = j then 1 else 0)
  have hφv (x : Fin n → ℝ) : φ x = v ⬝ᵥ x := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hpv : P *ᵥ v = 0 := by
    have hp : v ᵥ* P = 0 := by
      ext i
      have h := hφ (P *ᵥ Pi.single i 1) (LinearMap.mem_range_self (Matrix.toLin' P) _)
      rw [hφv, dotProduct_mulVec, dotProduct_single_one] at h
      exact h
    rwa [← mulVec_transpose, hsym] at hp
  rw [hφv]
  exact hy v hpv

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (hPeq : ReachGramianEq A N B P)
    (z : Fin n → ℝ) (hz : z ∈ LinearMap.range (Matrix.toLin' P)) (w : Fin m → ℝ) :
    field A N B z w ∈ LinearMap.range (Matrix.toLin' P) := by
  have hsym : Pᵀ = P := by simpa using hP.isHermitian.eq
  have hzorth (v : Fin n → ℝ) (hv : P *ᵥ v = 0) : v ⬝ᵥ z = 0 := by
    obtain ⟨x, rfl⟩ := hz
    change v ⬝ᵥ (P *ᵥ x) = 0
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, hv, zero_dotProduct]
  apply range_of_annihilates_kernel P hsym
  intro v hv
  obtain ⟨hn, hb⟩ := kernel_terms A N B P hP hPeq v hv
  have ha := kernel_A A N B P hP hPeq v hv
  have hAz : v ⬝ᵥ (A *ᵥ z) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose]
    exact hzorth _ ha
  have hNz (j : Fin m) : v ⬝ᵥ (N j *ᵥ z) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose]
    exact hzorth _ (hn j)
  have hBw : v ⬝ᵥ (B *ᵥ w) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hb, zero_dotProduct]
  simp only [field, dotProduct_add, dotProduct_sum, dotProduct_smul, hAz, hNz,
    hBw, smul_zero, Finset.sum_const_zero, add_zero]

#print axioms solution
