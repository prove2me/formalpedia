-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.inv_norm_sq_conj_ratio_pow_identities
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:52.379356+00:00
-- url     : https://prove2.me/submissions/591c3e82-535d-4541-b3f2-d8123ec64f04

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : InvNormSqConjRatioPowIdentities := by
  intro z g hz
  have hc : (starRingEnd ℂ) z ≠ 0 := (map_ne_zero _).mpr hz
  have hn : ‖z / (starRingEnd ℂ) z‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hz)]
  have hA : z ^ g ≠ 0 := pow_ne_zero g hz
  have hC : (starRingEnd ℂ) z ^ g ≠ 0 := pow_ne_zero g hc
  refine ⟨?_, ?_, ?_⟩
  · first
    | rw [norm_mul, norm_inv, norm_pow, norm_pow, hn, one_pow, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg z)]
    | simp [norm_mul, norm_inv, norm_pow, hn, Complex.normSq_nonneg, hz]
  · rw [← Complex.mul_conj, mul_pow, div_pow,
      show (starRingEnd ℂ) z ^ (2 * g) = ((starRingEnd ℂ) z ^ g) ^ 2 by ring]
    field_simp
    try ring
  · rw [← Complex.mul_conj, mul_pow, div_pow, show z ^ (2 * g) = (z ^ g) ^ 2 by ring]
    field_simp
    try ring
end Formalism.HermitianLattices.GlobalBoundRefinements
