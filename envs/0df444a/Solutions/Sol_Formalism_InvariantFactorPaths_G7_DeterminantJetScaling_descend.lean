-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.descend
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:06.720156+00:00
-- url     : https://prove2.me/submissions/f29a5666-864b-4957-96a5-51adfe6cea8f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EKernel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DeterminantJetScaling_norm_unif_pow

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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPairPoly minorProd mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
namespace Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] {ϖ : ℂ_[p]} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]))
    (d : ℕ) (g : ℝ) (x y : ℂ_[p]) (hxy : x = ϖ ^ d * y)
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(g + rhoP p * d))) : ‖y‖ ≤ (p : ℝ) ^ (-g) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [hxy, norm_mul, norm_unif_pow hϖ, neg_add, add_comm, Real.rpow_add hpos] at hx
  exact le_of_mul_le_mul_left hx (Real.rpow_pos_of_pos hpos _)
end Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
