-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.lowGe_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:41:11.438186+00:00
-- url     : https://prove2.me/submissions/a5dfde12-384f-4ac5-b4e0-a2c20983d550

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_lowDeg_add
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
theorem _root_.solution {m m' : ℕ} {V V' : MvPowerSeries (Tp ⊕ Lw) K} (h : LowGe m V) (h' : LowGe m' V') :
    LowGe (m + m') (V * V') := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  rw [← hx', lowDeg_add]
  exact add_le_add (h _ (left_ne_zero_of_mul hx0)) (h' _ (right_ne_zero_of_mul hx0))
end Formalism.InvariantFactorPaths.G7.ETerm
