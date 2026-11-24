-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.contOn_of_CkOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:34.381069+00:00
-- url     : https://prove2.me/submissions/bfe97a01-50a3-4948-a2ff-18c141cdd75d

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {F : Mat k r → E}
    (h : CkOn m (GV k r) F) : ContinuousOn F (GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', hfe⟩ := h g₀ hg₀
  have hc : ContinuousAt f' g₀ := hf'.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfe g₀ hg₀U hg₀)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hg₀U)] with g hg hgU
  exact hfe g hgU hg
end Formalism.FourierDecayAlt.P.B7
