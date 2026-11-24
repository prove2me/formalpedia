-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.tr_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:37:45.400192+00:00
-- url     : https://prove2.me/submissions/2ad9c0f2-f0e6-4f86-b1ab-50c653cd3e71

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_al_tr_eq

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (hC : ConjInv D) {p' : SS k r} (hp' : D.inSS p') :
    MeasurePreserving (tr p') D.μSS D.μSS := by
  rw [al_tr_eq]
  unfold RealPlaceData.μSS
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  refine MeasurePreserving.prod (MeasurePreserving.prod ?_ ?_) (MeasurePreserving.prod ?_ ?_)
  · exact ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarW.left _ h1⟩
  · exact MeasurePreserving.comp ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarN.left _ h2⟩
      ⟨(BesselUnitaryEquiv.continuous_conjM _).measurable, hC _ (Or.inl h1)⟩
  · exact ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarW'.left _ h3⟩
  · exact MeasurePreserving.comp ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarN.left _ h4⟩
      ⟨(BesselUnitaryEquiv.continuous_conjM _).measurable, hC _ (Or.inr h3)⟩
end Formalism.FourierDecayAlt.P.B7
