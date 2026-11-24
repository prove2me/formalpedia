-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.u_continuous_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:31:02.469819+00:00
-- url     : https://prove2.me/submissions/4456dd0f-96cb-4dd6-bebd-bda08bfd82ac

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_int_test
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_norm_om_integrand

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
theorem _root_.solution {w : ℝ → ℝ} (h : IsTest w) : Continuous (om w) := by
  have hw : Continuous w := h.1.continuous
  show Continuous fun x => ∫ τ : ℝ, (w τ : ℂ) * Complex.exp (Complex.I * ((τ * x : ℝ) : ℂ))
  refine continuous_of_dominated (bound := fun τ => ‖w τ‖) (fun x => ?_)
    (fun x => ae_of_all _ fun τ => (u_norm_om_integrand w x τ).le) (u_int_test h).norm (ae_of_all _ fun τ => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    first
      | exact (Complex.continuous_ofReal.comp hw).mul (Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const))))
      | fun_prop
  · first
      | exact continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))))
      | fun_prop
end Formalism.FourierDecayAlt.P.B7
