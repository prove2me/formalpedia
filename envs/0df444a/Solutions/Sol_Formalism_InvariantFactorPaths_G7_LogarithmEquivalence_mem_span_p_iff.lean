-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mem_span_p_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:41:23.648837+00:00
-- url     : https://prove2.me/submissions/9342154d-a84d-42d0-90cc-abdb8d0cb54d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mem_ballRing
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_coe_natCast_ball

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
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
namespace Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (x : ballRing K) :
    x ∈ Ideal.span {(p : ballRing K)} ↔ ‖(x : K)‖ ≤ (p : ℝ)⁻¹ := by
  have hpR : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hp.pos)
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact absurd hn hpR.ne
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    rw [Subring.coe_mul, coe_natCast_ball, norm_mul, hn]
    exact mul_le_of_le_one_left hpR.le a.2
  · intro h
    have ha : (x : K) / (p : K) ∈ ballRing K := by
      rw [mem_ballRing, norm_div, hn, div_inv_eq_mul]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      calc ‖(x : K)‖ * p ≤ (p : ℝ)⁻¹ * p := mul_le_mul_of_nonneg_right h hp0.le
        _ = 1 := inv_mul_cancel₀ hp0.ne'
    refine ⟨⟨_, ha⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, coe_natCast_ball]
    exact div_mul_cancel₀ _ hpK
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
