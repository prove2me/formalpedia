-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.jc_ae_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:43:37.107301+00:00
-- url     : https://prove2.me/submissions/a5364fc0-b15d-4e29-95b2-075ef7aebb12

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurableSet_Qset
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_lint
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_meas_E
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_formula

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
    ∀ᵐ q ∂(volume.restrict (Qset D)), jc_E D F q < ∞ := by
  have hc := jc_cont hF
  have h1 := jc_lint D hCC hF
  rw [jc_formula D hI hc] at h1
  have hm : Measurable fun q : (Fin r → ℂ) × ℂ =>
      ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) * jc_E D F q :=
    (ENNReal.measurable_ofReal.comp (measurable_bcWeight _ _)).mul (jc_meas_E D hc)
  have h2 := ae_lt_top hm h1.ne
  rw [ae_restrict_iff' (measurableSet_Qset D)]
  filter_upwards [h2] with q hq hqQ
  by_contra hcon
  have htop : jc_E D F q = ∞ := not_lt_top_iff.1 hcon
  rw [htop, ENNReal.mul_top] at hq
  · exact lt_irrefl _ hq
  · have : 0 < bcWeight k r (Tz k r D.z) (Tz k r D.z') q := hqQ
    simpa using this
end Formalism.FourierDecayAlt.P.B7
