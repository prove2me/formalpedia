-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.norm_unif_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:31.283968+00:00
-- url     : https://prove2.me/submissions/582d1145-fb3e-40c9-ac0b-5b1a54314f46

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementM
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MPlaces
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_norm_unif


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair mfact)
open Formalism.FG.IntegralSubstitution (integral_mul integralSubstV)
open TwoS
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {K : Type} [NormedField K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {ϖ : K} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K)) :
    ‖ϖ ^ (p + 1)‖ = (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
  have h2 : (p : ℝ) + 1 ≠ 0 := by intro h; linarith
  have h3 : (p : ℝ) ^ 2 - 1 ≠ 0 := by
    have : (p : ℝ) ^ 2 - 1 = ((p : ℝ) - 1) * ((p : ℝ) + 1) := by ring
    rw [this]
    exact mul_ne_zero h1 h2
  rw [norm_pow, norm_unif hp hn hϖ, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hp0),
    Real.inv_rpow hp0, Real.rpow_neg hp0]
  congr 2
  push_cast
  field_simp
  ring
end Formalism.InvariantFactorPaths.G7
