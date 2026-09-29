-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.rayleigh_eq_sum_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:55:22.987191+00:00
-- url     : https://prove2.me/submissions/1cfd63ea-602a-4ebd-92e3-25260c524188

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.rayleigh_eq_sum_eigenvalues
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_repr_apply_of_symmetric
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) :
    rayleigh T x = ∑ i, hT.eigenvalues hn i * ‖coeff hT hn x i‖ ^ 2 := by

  classical
  have hinner : inner ℂ x (T x)
      = inner ℂ ((hT.eigenvectorBasis hn).repr x) ((hT.eigenvectorBasis hn).repr (T x)) :=
    ((hT.eigenvectorBasis hn).repr.inner_map_map x (T x)).symm
  rw [rayleigh, hinner, PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hc : ((hT.eigenvectorBasis hn).repr (T x)).ofLp i
      = (hT.eigenvalues hn i : ℂ) * coeff hT hn x i := repr_apply_of_symmetric hT hn x i
  rw [show ((hT.eigenvectorBasis hn).repr x).ofLp i = coeff hT hn x i from rfl, hc,
    RCLike.inner_apply, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_mul, Complex.ofReal_re]
