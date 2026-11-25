-- Prove2me | solution 1 for Deduction.LFunction_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:03:26.016199+00:00
-- url     : https://prove2.me/submissions/f8154fe5-161d-4009-9c00-cd233a09ecf8

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Theorems.Thm_Deduction_LFunctionConjugation_ofReal_cpow_conj
import Theorems.Thm_Deduction_LFunctionConjugation_hurwitz_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (DirichletCharacter.LFunction χ s) := by
  simp only [DirichletCharacter.LFunction, ZMod.LFunction, map_mul, map_sum]
  congr 1
  · have h := LFunctionConjugation.ofReal_cpow_conj (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (-s)
    simpa using h
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [LFunctionConjugation.hurwitz_conj, ← MulChar.star_apply']
    rfl
end Deduction
