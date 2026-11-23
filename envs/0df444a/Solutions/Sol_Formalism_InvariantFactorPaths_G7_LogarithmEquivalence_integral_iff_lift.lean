-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_iff_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:40.516638+00:00
-- url     : https://prove2.me/submissions/1e6fcb3f-d992-4af5-89bc-334766bc77ad

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence

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
theorem _root_.solution {K ι : Type} [NormedField K] [IsUltrametricDist K]
    {f : MvPowerSeries ι K} :
    Integral f ↔ ∃ f₀ : MvPowerSeries ι (ballRing K), MvPowerSeries.map (ballRing K).subtype f₀ = f := by
  constructor
  · intro h
    have h' : ∀ n, MvPowerSeries.coeff n f ∈ ballRing K := h
    let f₀ : MvPowerSeries ι (ballRing K) := fun n => ⟨MvPowerSeries.coeff n f, h' n⟩
    refine ⟨f₀, ?_⟩
    ext n
    exact (MvPowerSeries.coeff_map _ _ _).trans rfl
  · rintro ⟨f₀, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n f₀).2
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
