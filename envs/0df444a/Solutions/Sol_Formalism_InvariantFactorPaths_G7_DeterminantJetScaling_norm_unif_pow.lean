-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.norm_unif_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:52.219877+00:00
-- url     : https://prove2.me/submissions/697dbd6f-f7ef-4cad-9a63-75cb9c51b3d9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EKernel
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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPairPoly minorProd mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
namespace Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] {ϖ : ℂ_[p]} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]))
    (d : ℕ) : ‖ϖ ^ d‖ = (p : ℝ) ^ (-(rhoP p * d)) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    have h : ‖(((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := PadicComplex.norm_extends' p _
    have h2 : (((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by simp
    rw [h2] at h
    rw [h, Padic.norm_p]
  rw [norm_pow, norm_unif hp.out hn hϖ, Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  unfold rhoP
  congr 1
  ring
end Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
