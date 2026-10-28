-- Prove2me | solution 1 for CountingMatroid.Analysis.ConnectedLaplacianKernel.connected_laplacian_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:28:03.187003+00:00
-- url     : https://prove2.me/submissions/669a1878-c672-426f-8e3a-cbaee752a9f9

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic
import Theorems.Thm_CountingMatroid_Analysis_ConnectedLaplacianKernel_laplacian_energy

namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
set_option autoImplicit false

namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConnectedLaplacianKernel

open scoped BigOperators

/-- INTERNAL: A connected nonnegative Laplacian has only constant active
fixed vectors. A zero weighted mean forces their matrix image to vanish. -/
theorem solution {σ : Type} [Fintype σ] [DecidableEq σ]
    (C : Matrix σ σ ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hsym : ∀ i j, C i j = C j i)
    (hcross : ∀ U : Set σ,
      (∃ i j, C i j ≠ 0 ∧ i ∈ U) →
      (∃ i j, C i j ≠ 0 ∧ i ∉ U) →
      ∃ i j, C i j ≠ 0 ∧ i ∈ U ∧ j ∉ U)
    (x : σ → ℝ)
    (hfixed : ∀ i, C.mulVec x i = (∑ j, C i j) * x i)
    (hmean : ∑ i, (∑ j, C i j) * x i = 0) : C.mulVec x = 0 := by
  classical
  have henergy : (∑ i, ∑ j, C i j * (x i - x j)^2) = 0 := by
    have he := laplacian_energy C hsym x
    simp only [hfixed] at he
    have hh : (∑ i, (∑ j, C i j) * (x i)^2) =
        ∑ i, x i * ((∑ j, C i j) * x i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hh, sub_self] at he
    linarith
  have hedge (i j : σ) (hij : C i j ≠ 0) : x i = x j := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => mul_nonneg (hC i j) (sq_nonneg _)))).mp
      henergy i (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (hC i j) (sq_nonneg _))).mp hi j (Finset.mem_univ j)
    have hp : 0 < C i j := lt_of_le_of_ne (hC i j) (Ne.symm hij)
    have hz : (x i - x j)^2 = 0 := (mul_eq_zero.mp hj).resolve_left hij
    nlinarith [sq_nonneg (x i - x j)]
  by_cases hz : C = 0
  · simp [hz]
  have hex : ∃ a b, C a b ≠ 0 := by
    by_contra h
    apply hz
    ext a b
    simpa using not_exists.mp (not_exists.mp h a) b
  obtain ⟨a, b, hab⟩ := hex
  have hconstant (i j : σ) (hij : C i j ≠ 0) : x i = x a := by
    by_contra hi
    obtain ⟨p, q, hpq, hp, hq⟩ := hcross {i | x i = x a}
      ⟨a, b, hab, rfl⟩ ⟨i, j, hij, hi⟩
    exact hq ((hedge p q hpq).symm.trans hp)
  have hsum : (∑ i, (∑ j, C i j) * x i) =
      (∑ i, ∑ j, C i j) * x a := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : C i j = 0
    · simp [hij]
    · rw [hconstant i j hij]
  have htotal : 0 < ∑ i, ∑ j, C i j := by
    apply Finset.sum_pos_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC i j)) |>.mpr
    refine ⟨a, Finset.mem_univ a, ?_⟩
    apply Finset.sum_pos_iff_of_nonneg (fun j _ => hC a j) |>.mpr
    exact ⟨b, Finset.mem_univ b, lt_of_le_of_ne (hC a b) (Ne.symm hab)⟩
  have hxa : x a = 0 := (mul_eq_zero.mp (hsum.symm.trans hmean)).resolve_left htotal.ne'
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : C i j = 0
  · simp [hij]
  · rw [← hedge i j hij, hconstant i j hij, hxa, mul_zero]
