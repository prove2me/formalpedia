-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.tr_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:09:58.150313+00:00
-- url     : https://prove2.me/submissions/085573ec-4615-4c48-9b1c-7dd85b5be073

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p' : SS k r} (hp' : D.inSS p') :
    MeasurableEmbedding (tr (k := k) (r := r) p') := by
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  have u1 := WeylGroupFacts.isUnit_of_uh h1.1
  have u2 := WeylGroupFacts.isUnit_of_uh h2.1
  have u3 := WeylGroupFacts.isUnit_of_uh h3.1
  have u4 := WeylGroupFacts.isUnit_of_uh h4.1
  let Φ : SS k r ≃ᵐ SS k r :=
    ((BesselUnitaryEquiv.lmulE _ u1).prodCongr ((BesselUnitaryEquiv.conjE _ u1).trans (BesselUnitaryEquiv.lmulE _ u2))).prodCongr
      ((BesselUnitaryEquiv.lmulE _ u3).prodCongr ((BesselUnitaryEquiv.conjE _ u3).trans (BesselUnitaryEquiv.lmulE _ u4)))
  exact Φ.measurableEmbedding
end Formalism.FourierDecayAlt.P.B7
