-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.integral_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:54.632266+00:00
-- url     : https://prove2.me/submissions/06738d32-455c-4e39-b311-2fd0c6188b74

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_integral_mul
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul


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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution {σ : Type} {f : MvPowerSeries σ K} (hf : Integral f) (i : ℕ) :
    Integral (f ^ i) := by
  classical
  induction i with
  | zero =>
    intro n
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ i ih =>
    rw [pow_succ]
    exact integral_mul ih hf
end Formalism.InvariantFactorPaths.G7.ETerm
