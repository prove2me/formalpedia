-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.sm_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:07.954024+00:00
-- url     : https://prove2.me/submissions/e8433e22-ab24-4829-8f6f-aeeb76222562

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_A

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
attribute [local instance] sfG sfW sfN sfW' sfSS
attribute [local instance] properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r =>
      xiTau D b.1.1 b.2 • RM D F b.2 (gqM D b.1.2) := by
  have hx : Measurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => xiTau D b.1.1 b.2 := by
    first
      | exact (measurable_xi D).comp (measurable_fst.fst.prodMk measurable_snd)
      | exact (measurable_xi D).comp (measurable_fst.fst.prod_mk measurable_snd)
  exact hx.stronglyMeasurable.smul (sm_A D hF)
end Formalism.FourierDecayAlt.P.B7
