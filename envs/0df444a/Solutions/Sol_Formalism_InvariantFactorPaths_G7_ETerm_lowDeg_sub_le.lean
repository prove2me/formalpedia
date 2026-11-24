-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.lowDeg_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:05.287498+00:00
-- url     : https://prove2.me/submissions/04c89458-bd50-41aa-901f-eb512afd1991

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
variable {Tp Lw : Type}
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution [Fintype Lw] (a c : Tp ⊕ Lw →₀ ℕ) : lowDeg (a - c) ≤ lowDeg a := by
  unfold lowDeg
  refine Finset.sum_le_sum fun x _ => ?_
  simp
end Formalism.InvariantFactorPaths.G7.ETerm
