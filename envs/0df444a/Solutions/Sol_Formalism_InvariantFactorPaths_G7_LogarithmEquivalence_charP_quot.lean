-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.charP_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:45:50.510026+00:00
-- url     : https://prove2.me/submissions/ab6ec219-f53b-4c65-84fc-e32f5e3f92d5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mem_span_p_iff

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
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) : CharP (ballRing K ⧸ Ideal.span {(p : ballRing K)}) p := by
  have hne : Ideal.span {(p : ballRing K)} ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, mem_span_p_iff hp hn]
    rw [Subring.coe_one, norm_one, not_le]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have : Nontrivial (ballRing K ⧸ Ideal.span {(p : ballRing K)}) := Ideal.Quotient.nontrivial_iff.2 hne
  rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (Ideal.Quotient.mk _) p,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
