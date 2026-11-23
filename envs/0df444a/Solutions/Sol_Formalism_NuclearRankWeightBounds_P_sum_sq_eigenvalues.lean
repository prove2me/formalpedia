-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.sum_sq_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:00.998978+00:00
-- url     : https://prove2.me/submissions/9d3310e2-3f8d-4c83-b3dc-428581a9b2c7

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset Matrix
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Y.IsHermitian) :
    ∑ j, hY.eigenvalues j ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 := by
  set U : Matrix (Fin N) (Fin N) ℂ := (hY.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hUdef
  set D : Matrix (Fin N) (Fin N) ℂ := diagonal (RCLike.ofReal ∘ hY.eigenvalues) with hDdef
  have hsp : Y = U * D * star U := by
    conv_lhs => rw [hY.spectral_theorem]
    rfl
  have hu : star U * U = 1 := Unitary.coe_star_mul_self hY.eigenvectorUnitary
  have h1 : (Y * Y).trace = (D * D).trace := by
    have : Y * Y = U * (D * D) * star U := by
      rw [hsp]
      simp only [mul_assoc]
      rw [← mul_assoc (star U) U, hu, one_mul]
    rw [this, trace_mul_cycle, hu, one_mul]
  have h2 : (D * D).trace = ∑ j, ((hY.eigenvalues j ^ 2 : ℝ) : ℂ) := by
    rw [hDdef, diagonal_mul_diagonal, trace_diagonal]
    simp [pow_two]
  have h3 : (Y * Y).trace = ∑ a, ∑ b, ((‖Y a b‖ ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [show Y * Y = Yᴴ * Y by rw [hY.eq]]
    simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show star (Y a b) = (starRingEnd ℂ) (Y a b) from rfl, Complex.conj_mul']
    push_cast; ring
  have h4 : ((∑ j, hY.eigenvalues j ^ 2 : ℝ) : ℂ) = ((∑ a, ∑ b, ‖Y a b‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum]
    rw [← h3, h1, h2]
  exact_mod_cast h4
end Formalism.NuclearRankWeightBounds.P
