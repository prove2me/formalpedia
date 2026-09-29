-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:16:13.354017+00:00
-- url     : https://prove2.me/submissions/71987bf1-7e6f-4d79-ae57-22b372881e83

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_repr_apply_of_symmetric
import Theorems.Thm_BookProof_SirkFinitePrecision_norm_sq_eq_sum_repr
import Theorems.Thm_BookProof_SirkFinitePrecision_index_nonempty
import Theorems.Thm_BookProof_SirkFinitePrecision_hasRealEigenvalue_eigenvalues
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : x ≠ 0) (θ : ℝ) :
    ∃ lam : ℝ, HasRealEigenvalue T lam ∧ |lam - θ| * ‖x‖ ≤ ‖T x - (θ : ℂ) • x‖ := by

  classical
  obtain ⟨i0, -, hi0⟩ :=
    Finset.exists_min_image univ (fun i => |hT.eigenvalues hn i - θ|)
      (index_nonempty hT hn hx)
  refine ⟨hT.eigenvalues hn i0, hasRealEigenvalue_eigenvalues hT hn i0, ?_⟩
  have hd0 : 0 ≤ |hT.eigenvalues hn i0 - θ| := abs_nonneg _
  have hcoord : ∀ i : Fin n, coeff hT hn (T x - (θ : ℂ) • x) i
      = ((hT.eigenvalues hn i : ℂ) - θ) * coeff hT hn x i := by
    intro i
    have h := repr_apply_of_symmetric hT hn x i
    simp only [coeff] at h ⊢
    rw [map_sub, map_smul]
    have hsub : (((hT.eigenvectorBasis hn).repr (T x))
          - (θ : ℂ) • ((hT.eigenvectorBasis hn).repr x)).ofLp i
        = ((hT.eigenvectorBasis hn).repr (T x)).ofLp i
          - (θ : ℂ) * ((hT.eigenvectorBasis hn).repr x).ofLp i := by simp
    rw [hsub, h]
    ring
  have key : (|hT.eigenvalues hn i0 - θ| * ‖x‖) ^ 2 ≤ ‖T x - (θ : ℂ) • x‖ ^ 2 := by
    rw [mul_pow, norm_sq_eq_sum_repr hT hn x, norm_sq_eq_sum_repr hT hn (T x - (θ : ℂ) • x),
      Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    rw [hcoord i, norm_mul]
    have hle : |hT.eigenvalues hn i0 - θ| ≤ ‖((hT.eigenvalues hn i : ℂ) - θ)‖ := by
      have := hi0 i (mem_univ i)
      simpa [← Complex.ofReal_sub] using this
    have hb0 : (0 : ℝ) ≤ ‖coeff hT hn x i‖ := norm_nonneg _
    have hsq : |hT.eigenvalues hn i0 - θ| ^ 2 ≤ ‖((hT.eigenvalues hn i : ℂ) - θ)‖ ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg ‖coeff hT hn x i‖]
  have h1 : 0 ≤ |hT.eigenvalues hn i0 - θ| * ‖x‖ := by positivity
  exact (sq_le_sq₀ h1 (norm_nonneg _)).mp key
