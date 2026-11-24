-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.jc_lint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:41:02.230194+00:00
-- url     : https://prove2.me/submissions/917744b9-9109-4a7a-bb15-385fe8052597

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_ae_FM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_aesm_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_bound

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {A : ℝ} (hCC : CCIntegrable D A) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : InCC A 4 F) : (∫⁻ g, ‖FM F g‖ₑ ∂D.μG) < ∞ := by
  obtain ⟨c, hc⟩ := jc_bound hF
  have h := hCC F c (jc_aesm_F D (jc_cont hF)) hc
  have e : (∫⁻ g, ‖FM F g‖ₑ ∂D.μG) = ∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂D.μG := by
    refine lintegral_congr_ae ?_
    filter_upwards [jc_ae_FM D F] with g hg
    rw [hg]
  rw [e]
  exact h
end Formalism.FourierDecayAlt.P.B7
