-- Prove2me | solution 1 for FiniteSampleDependence.Rigidity.nonnegativity_permutation_invariance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:00:25.458765+00:00
-- url     : https://prove2.me/submissions/65142157-b906-435a-b75a-215ce0cd264d

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model

section
set_option autoImplicit false

namespace FiniteSampleDependence.Dev.Lem21

open FiniteSampleDependence.Rigidity Matrix

lemma mul_mem_simplex {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsColumnStochastic T)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) : T * U ∈ simplex n m := by
  obtain ⟨hT0, hT1⟩ := hT
  obtain ⟨hU0, hU1⟩ := hU
  refine ⟨fun i α => ?_, ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hT0 _ _) (hU0 _ _)
  · unfold tau at hU1 ⊢
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc ∑ α, ∑ i, ∑ k, T i k * U k α = ∑ α, ∑ k, ∑ i, T i k * U k α := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_comm
      _ = ∑ α, ∑ k, U k α := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_mul, hT1 k, one_mul]
      _ = ∑ i, ∑ α, U i α := by rw [Finset.sum_comm]
      _ = 1 := hU1

lemma rank_ne_zero_of_ne_zero {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (h : A ≠ 0) :
    A.rank ≠ 0 := by
  intro h0
  apply h
  unfold Matrix.rank at h0
  have := Submodule.finrank_eq_zero.mp h0
  ext i j
  have h1 : A.mulVecLin (Pi.single j 1) = 0 := by
    have hm : A.mulVecLin (Pi.single j 1) ∈ LinearMap.range A.mulVecLin := ⟨_, rfl⟩
    rw [this] at hm
    simpa using hm
  have := congrFun h1 i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this

lemma perm_le {n m : ℕ} (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hF : LFDPI F)
    (σ : Equiv.Perm (Fin n)) (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) :
    F (σ.permMatrix ℝ * U) ≤ F U := by
  apply hF U hU
  refine ⟨fun i j => ?_, fun j => ?_⟩
  · simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  · simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    rw [Finset.sum_eq_single (σ.symm j)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [← h]; simp
    · simp

lemma perm_cs {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsColumnStochastic (σ.permMatrix ℝ) := by
  refine ⟨fun i j => ?_, fun j => ?_⟩
  · simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  · simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    rw [Finset.sum_eq_single (σ.symm j)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [← h]; simp
    · simp

lemma inv_mul_perm {n m : ℕ} (σ : Equiv.Perm (Fin n)) (U : Matrix (Fin n) (Fin m) ℝ) :
    σ⁻¹.permMatrix ℝ * (σ.permMatrix ℝ * U) = U := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp

lemma nonneg {n m : ℕ} (hn : 2 ≤ n) (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hF : LFDPI F)
    (hZ : IZ F) (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) : 0 ≤ F U := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let T : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun _ _ => 1 / (n : ℝ)
  have hT : IsColumnStochastic T := by
    refine ⟨fun i j => by simp [T], fun j => ?_⟩
    simp [T]
    field_simp
  have hTU : T * U = Matrix.vecMulVec (fun _ => 1 / (n : ℝ)) (colMarginal U) := by
    ext i α
    simp [T, Matrix.mul_apply, Matrix.vecMulVec_apply, colMarginal, ← Finset.mul_sum]
  have hmem := mul_mem_simplex T hT U hU
  have hr : (T * U).rank = 1 := by
    apply le_antisymm
    · rw [hTU]; exact Matrix.rank_vecMulVec_le _ _
    · apply Nat.one_le_iff_ne_zero.mpr
      apply rank_ne_zero_of_ne_zero
      intro h0
      have h1 := hmem.2
      rw [h0] at h1
      simp [tau] at h1
  have := hF U hU T hT
  rw [hZ _ hmem hr] at this
  exact this

end FiniteSampleDependence.Dev.Lem21

namespace FiniteSampleDependence.Rigidity

theorem chk_nonnegativity_permutation_invariance {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) :
    (LFDPI F → IZ F → ∀ U ∈ simplex n m, 0 ≤ F U) ∧
    (LFDPI F → ∀ σ : Equiv.Perm (Fin n), ∀ U ∈ simplex n m,
      F (σ.permMatrix ℝ * U) = F U) := by
  refine ⟨fun hF hZ U hU => Dev.Lem21.nonneg hn F hF hZ U hU, fun hF σ U hU => ?_⟩
  apply le_antisymm (Dev.Lem21.perm_le F hF σ U hU)
  have h := hF (σ.permMatrix ℝ * U) (Dev.Lem21.mul_mem_simplex _ (Dev.Lem21.perm_cs σ) U hU)
    (σ⁻¹.permMatrix ℝ) (Dev.Lem21.perm_cs _)
  rwa [Dev.Lem21.inv_mul_perm] at h

end FiniteSampleDependence.Rigidity
end

theorem solution : type_of% @FiniteSampleDependence.Rigidity.chk_nonnegativity_permutation_invariance := @FiniteSampleDependence.Rigidity.chk_nonnegativity_permutation_invariance
