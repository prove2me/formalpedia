-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_quad_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:49.225027+00:00
-- url     : https://prove2.me/submissions/44411c87-28b2-46d3-848f-b95c9cdfd2c8

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (d : ι → ℂ) :
    star ((hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ d) ⬝ᵥ
        (A *ᵥ ((hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ d)) =
      ∑ i, ((hA.eigenvalues i * Complex.normSq (d i) : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef
  have hU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hs : A = U * D * star U := hA.spectral_theorem
  have hAU : A * U = U * D := by
    calc A * U = U * D * star U * U := by rw [← hs]
      _ = U * D * (star U * U) := by simp only [Matrix.mul_assoc]
      _ = U * D := by rw [hU, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  simp only [_root_.dotProduct, hDdef, Matrix.mulVec_diagonal, Function.comp_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : star (d i) * d i = (Complex.normSq (d i) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    first | rfl | skip
  have h2 : (RCLike.ofReal (hA.eigenvalues i) : ℂ) = ((hA.eigenvalues i : ℝ) : ℂ) := rfl
  rw [Complex.ofReal_mul, ← h1, h2]
  ring
end Formalism.QuantumDeterminants
