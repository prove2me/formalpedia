-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.continuous_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:18.184853+00:00
-- url     : https://prove2.me/submissions/74c111a7-639f-4521-9fae-f9aa7ba6c14d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
import Theorems.Thm_Formalism_FG_InjVAux_Good_mul
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mul


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
open Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
open MvPowerSeries
namespace Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
theorem _root_.solution {R τ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalSemiring R]
    (e : τ) :
    let := WithPiTopology.instTopologicalSpace (σ := τ) (R := R)
    Continuous (fun f : MvPowerSeries τ R => pderiv R e f) := by
  let := WithPiTopology.instTopologicalSpace (σ := τ) (R := R)
  refine continuous_pi fun n => ?_
  have : (fun f : MvPowerSeries τ R => (pderiv R e f) n) =
      fun f => coeff (n + Finsupp.single e 1) f * ((n e : R) + 1) := by
    funext f
    exact coeff_pderiv f n
  rw [this]
  exact (WithPiTopology.continuous_coeff R _).mul continuous_const
end Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
