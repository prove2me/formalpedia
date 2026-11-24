-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.measurable_sgsM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:57:52.831798+00:00
-- url     : https://prove2.me/submissions/3b351561-6d42-4c6e-8842-825638473e05

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_invM
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
attribute [local instance] sfG sfW sfN sfW' sfSS
attribute [local instance] properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution : Measurable fun a : SS k r × Mt k r => sgsM a.1 a.2 := by
  have e : (fun a : SS k r × Mt k r => sgsM a.1 a.2) = fun a =>
      mulM (mulM (mulM (mulM (invM a.1.1.1) (invM a.1.1.2)) a.2) a.1.2.2) a.1.2.1 :=
    funext fun a => sgsM_eq a.1 a.2
  rw [e]
  exact meas_mulM (meas_mulM (meas_mulM (meas_mulM (measurable_invM.comp measurable_fst.fst.fst)
    (measurable_invM.comp measurable_fst.fst.snd)) measurable_snd) measurable_fst.snd.snd) measurable_fst.snd.fst
end Formalism.FourierDecayAlt.P.B7
