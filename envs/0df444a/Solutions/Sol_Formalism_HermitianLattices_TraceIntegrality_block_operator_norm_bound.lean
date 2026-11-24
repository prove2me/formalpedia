-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.block_operator_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:45.998617+00:00
-- url     : https://prove2.me/submissions/49858960-5d67-4814-ba04-df7a8298e7b6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BlockOperatorNormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open MeasureTheory Finset
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : BlockOperatorNormBound := by
  intro X X' V V' _ _ _ _ _ _ A φ β hβ
  have hφ : 0 ≤ ∑ x, ‖φ x‖ ^ 2 := Finset.sum_nonneg (fun x _ => by positivity)
  have h1 : ∑ x', ‖∑ x, A x' x (φ x)‖ ^ 2 ≤ (∑ x', ∑ x, ‖A x' x‖ ^ 2) * ∑ x, ‖φ x‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun x' _ => ?_)
    have h2 : ‖∑ x, A x' x (φ x)‖ ≤ ∑ x, ‖A x' x‖ * ‖φ x‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _ => (A x' x).le_opNorm (φ x)))
    calc ‖∑ x, A x' x (φ x)‖ ^ 2 ≤ (∑ x, ‖A x' x‖ * ‖φ x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ ≤ (∑ x, ‖A x' x‖ ^ 2) * ∑ x, ‖φ x‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  refine ⟨h1, h1.trans (mul_le_mul_of_nonneg_right ?_ hφ)⟩
  calc ∑ x', ∑ x, ‖A x' x‖ ^ 2 ≤ ∑ _x' : X', ∑ _x : X, β :=
        Finset.sum_le_sum (fun x' _ => Finset.sum_le_sum (fun x _ => hβ x' x))
    _ = (Fintype.card X' : ℝ) * Fintype.card X * β := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
end Formalism.HermitianLattices.TraceIntegrality
