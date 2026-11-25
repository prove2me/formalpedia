-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.jc_ae_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:39.254023+00:00
-- url     : https://prove2.me/submissions/c811accd-2839-4e98-9627-636ff4481e53

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_mem_good_set_restrict
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_ae_E
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_integrable_of

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) {A : ℝ} (hCC : CCIntegrable D A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∀ᵐ q ∂(volume.restrict (Qset D)), Integrable (fun p => rho D p F (gq D q)) D.μSS := by
  filter_upwards [jc_ae_E D hI hCC hF, ae_mem_good_set_restrict D] with q hE hq
  exact jc_integrable_of D (jc_cont hF) hq hE
end Formalism.FourierDecayAlt.P.B7
