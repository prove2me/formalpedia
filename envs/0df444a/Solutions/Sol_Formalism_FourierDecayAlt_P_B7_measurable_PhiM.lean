-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.measurable_PhiM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:57:49.986278+00:00
-- url     : https://prove2.me/submissions/31f5a00c-78c4-4dd5-aea8-f63776f85e88

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_invM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_gqM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_meas_mulM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sgsM_eq

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : Measurable (PhiM D) := by
  have e : PhiM D = fun a : ((Fin r → ℂ) × ℂ) × SS k r =>
      mulM (mulM (mulM (mulM (invM a.2.1.1) (invM a.2.1.2)) (gqM D a.1)) a.2.2.2) a.2.2.1 :=
    funext fun a => sgsM_eq a.2 (gqM D a.1)
  rw [e]
  exact meas_mulM (meas_mulM (meas_mulM (meas_mulM (measurable_invM.comp measurable_snd.fst.fst)
    (measurable_invM.comp measurable_snd.fst.snd)) ((measurable_gqM D).comp measurable_fst))
    measurable_snd.snd.snd) measurable_snd.snd.fst
end Formalism.FourierDecayAlt.P.B7
