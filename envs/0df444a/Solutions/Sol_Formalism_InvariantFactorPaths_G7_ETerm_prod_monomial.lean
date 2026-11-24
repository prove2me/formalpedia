-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.prod_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:05.8788+00:00
-- url     : https://prove2.me/submissions/60c97e03-a4ae-418f-aead-0907b8d21344

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right


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
open Formalism.InvariantFactorPaths.G7.ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
variable {K σ : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution {α : Type} (s : Finset α) (d : α → σ →₀ ℕ) (a : α → K) :
    ∏ i ∈ s, MvPowerSeries.monomial (d i) (a i) =
      MvPowerSeries.monomial (∑ i ∈ s, d i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MvPowerSeries.monomial_zero_one]
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.prod_insert hx, ih,
      MvPowerSeries.monomial_mul_monomial]
end Formalism.InvariantFactorPaths.G7.ETerm
