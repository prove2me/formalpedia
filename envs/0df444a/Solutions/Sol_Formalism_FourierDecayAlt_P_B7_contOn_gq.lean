-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.contOn_gq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:15:43.86902+00:00
-- url     : https://prove2.me/submissions/102c7763-ab27-4291-bfba-f32579a51c24

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
attribute [local instance] sfG sfW sfN sfW'
attribute [local instance] sfSS
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : ContinuousOn (gqF D) (Q0 D) := by
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  simp only [gqF, gq, bigCell]
  split_ifs with h1 h2 h3 h4 h5
  · exact ((continuous_apply _).comp continuous_fst).continuousOn
  · exact continuousOn_const
  · exact ((D.sec.1 _ _).continuousOn).comp continuous_snd.continuousOn fun q hq => hq.2
  · exact continuousOn_const
  · refine ContinuousOn.inv₀ (continuous_star.comp ((continuous_apply _).comp continuous_fst)).continuousOn ?_
    intro q hq
    simpa using hq.1 _
  · exact continuousOn_const
end Formalism.FourierDecayAlt.P.B7
