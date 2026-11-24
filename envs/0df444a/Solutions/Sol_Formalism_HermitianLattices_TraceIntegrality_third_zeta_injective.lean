-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.third_zeta_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:39.022019+00:00
-- url     : https://prove2.me/submissions/ab72dc8e-6c89-4497-9b64-7684bfc4fc86

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HookRowProductEqFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : InjectiveReindexNormLe := by
  intro X X' V V' _ _ _ _ _ _ e P φ he
  calc ∑ x', ‖P (φ (e x'))‖ ^ 2 ≤ ∑ x', ‖P‖ ^ 2 * ‖φ (e x')‖ ^ 2 := by
        refine Finset.sum_le_sum fun x' _ => ?_
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (P.le_opNorm _) 2
    _ = ‖P‖ ^ 2 * ∑ x', ‖φ (e x')‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ‖P‖ ^ 2 * ∑ x, ‖φ x‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ x', ‖φ (e x')‖ ^ 2 = ∑ x ∈ (univ : Finset X').map ⟨e, he⟩, ‖φ x‖ ^ 2 := by
              rw [Finset.sum_map]; rfl
          _ ≤ ∑ x, ‖φ x‖ ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun x _ _ => by positivity)
end Formalism.HermitianLattices.TraceIntegrality
