-- Prove2me | solution 1 for CountingMatroid.Analysis.ConnectedLaplacianKernel.laplacian_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:47:02.174052+00:00
-- url     : https://prove2.me/submissions/71425d89-61f9-48b2-ac40-39da089f4c45

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic

namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
set_option autoImplicit false

namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConnectedLaplacianKernel

open scoped BigOperators

/-- INTERNAL: The symmetric Laplacian energy identity, including zero rows. -/
theorem solution {σ : Type} [Fintype σ] (C : Matrix σ σ ℝ)
    (hsym : ∀ i j, C i j = C j i) (x : σ → ℝ) :
    (∑ i, (∑ j, C i j) * (x i)^2) - (∑ i, x i * C.mulVec x i) =
      (∑ i, ∑ j, C i j * (x i - x j)^2) / 2 := by
  have hswap : (∑ i, ∑ j, C i j * (x j)^2) =
      ∑ i, ∑ j, C i j * (x i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  have hexp : (∑ i, ∑ j, C i j * (x i - x j)^2) =
      (∑ i, ∑ j, C i j * (x i)^2) + (∑ i, ∑ j, C i j * (x j)^2) -
      2 * (∑ i, ∑ j, x i * (C i j * x j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexp, hswap]
  ring
