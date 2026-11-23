-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.norm_coeff_dlgF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:32.558803+00:00
-- url     : https://prove2.me/submissions/b4213e37-fbe7-4629-9a6d-ffc34ec918c6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow


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
open Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
open MvPowerSeries
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (N : ℕ) :
    ‖PowerSeries.coeff N (PowerSeries.derivative K (lgF K p))‖ ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpK : (p : K) ≠ 0 := by
    rw [← norm_pos_iff, hnp]
    positivity
  rw [PowerSeries.coeff_derivative]
  by_cases h : PowerSeries.coeff (N + 1) (lgF K p) = 0
  · simp [h]
  obtain ⟨j, hj⟩ := coeff_lgF_ne_zero h
  have e : PowerSeries.coeff (N + 1) (lgF K p) * ((N : K) + 1) = (p : K) ^ j := by
    have hc : ((N : K) + 1) = (((p ^ 2) ^ j : ℕ) : K) := by
      rw [← hj]
      push_cast
      ring
    rw [hc, hj, coeff_lgF_pow K hp.two_le]
    push_cast
    field_simp
    ring
  rw [e, norm_pow, hnp]
  exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_lt.le))
end Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
