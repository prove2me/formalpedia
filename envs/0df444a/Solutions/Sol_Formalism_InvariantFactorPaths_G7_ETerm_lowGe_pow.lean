-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.lowGe_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:50.292799+00:00
-- url     : https://prove2.me/submissions/9f119ec3-c4ee-4f66-82d8-92b2c0cb6059

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_lowGe_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_lowGe_mul
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
variable {K Tp Lw : Type} [Field K] [Fintype Lw]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution {m : ℕ} {V : MvPowerSeries (Tp ⊕ Lw) K} (h : LowGe m V) (i : ℕ) :
    LowGe (m * i) (V ^ i) := by
  induction i with
  | zero => exact lowGe_zero _
  | succ i ih =>
    rw [pow_succ, Nat.mul_succ]
    exact lowGe_mul ih h
end Formalism.InvariantFactorPaths.G7.ETerm
