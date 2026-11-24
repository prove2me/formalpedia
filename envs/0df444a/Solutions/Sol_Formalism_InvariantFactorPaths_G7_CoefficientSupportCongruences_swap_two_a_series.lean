-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.swap_two_a_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:36:51.825084+00:00
-- url     : https://prove2.me/submissions/afc2ea72-fa80-4b51-9e53-e826eddd308e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_swap2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_coeff_swap2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
open FrobeniusSubstitution
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
theorem _root_.solution (p : ℕ) (x y : Fin 2) (hx : Equiv.swap (0 : Fin 2) 1 x = y)
    (hy : Equiv.swap (0 : Fin 2) 1 y = x) : swap2 (AA K p x y) = AA K p y x := by
  ext n
  rw [Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_swap2]
  have h1 : (Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.sw n) x = n y := by
    show n ((Equiv.swap (0 : Fin 2) 1).symm x) = n y
    rw [Equiv.symm_swap, hx]
  have h2 : (Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.sw n) y = n x := by
    show n ((Equiv.swap (0 : Fin 2) 1).symm y) = n x
    rw [Equiv.symm_swap, hy]
  show AA K p x y (Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.sw n) = AA K p y x n
  simp only [AA, h1, h2]
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
