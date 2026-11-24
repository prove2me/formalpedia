-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.jc_cont_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:37:56.777228+00:00
-- url     : https://prove2.me/submissions/ae7b3ede-f191-4837-87aa-6f2a08b6acb6

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_continuous_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_norm_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_xi

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r)
    (h : Integrable (fun p => rho D p F g) D.μSS) : Continuous fun τ => Jtau D τ F g := by
  show Continuous fun τ => ∫ p, xiTau D τ p • rho D p F g ∂D.μSS
  have hxm : ∀ τ : ℝ × ℝ, Measurable fun p : SS k r => xiTau D τ p := fun τ => by
    first
      | exact (measurable_xi D).comp (measurable_const.prodMk measurable_id)
      | exact (measurable_xi D).comp (measurable_const.prod_mk measurable_id)
  refine continuous_of_dominated (bound := fun p => ‖rho D p F g‖) (fun τ => ?_)
    (fun τ => ae_of_all _ fun p => ?_) h.norm (ae_of_all _ fun p => ?_)
  · exact (hxm τ).aestronglyMeasurable.smul h.aestronglyMeasurable
  · simp [norm_smul, norm_xi]
  · first
      | exact ((continuous_xi D).comp (continuous_id.prodMk continuous_const)).smul continuous_const
      | exact ((continuous_xi D).comp (continuous_id.prod_mk continuous_const)).smul continuous_const
end Formalism.FourierDecayAlt.P.B7
