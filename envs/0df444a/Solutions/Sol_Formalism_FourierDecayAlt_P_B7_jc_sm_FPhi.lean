-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.jc_sm_FPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:57:52.079037+00:00
-- url     : https://prove2.me/submissions/07e2a8b5-279a-43e8-8e61-93082c01517a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_invM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_gqM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_FM
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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun a : ((Fin r → ℂ) × ℂ) × SS k r => FM F (sgsM a.2 (gqM D a.1)) := by
  have hs : Measurable fun a : ((Fin r → ℂ) × ℂ) × SS k r => sgsM a.2 (gqM D a.1) := by
    have e : (fun a : ((Fin r → ℂ) × ℂ) × SS k r => sgsM a.2 (gqM D a.1)) = fun a =>
        mulM (mulM (mulM (mulM (invM a.2.1.1) (invM a.2.1.2)) (gqM D a.1)) a.2.2.2) a.2.2.1 :=
      funext fun a => sgsM_eq a.2 (gqM D a.1)
    rw [e]
    exact meas_mulM (meas_mulM (meas_mulM (meas_mulM (measurable_invM.comp measurable_snd.fst.fst)
      (measurable_invM.comp measurable_snd.fst.snd)) ((measurable_gqM D).comp measurable_fst))
      measurable_snd.snd.snd) measurable_snd.snd.fst
  have f2 : StronglyMeasurable fun a : ((Fin r → ℂ) × ℂ) × SS k r => FM F (sgsM a.2 (gqM D a.1)) :=
    (sm_FM hF).comp_measurable hs
  exact f2
end Formalism.FourierDecayAlt.P.B7
