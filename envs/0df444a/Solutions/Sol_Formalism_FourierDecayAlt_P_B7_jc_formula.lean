-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.jc_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:18:13.165151+00:00
-- url     : https://prove2.me/submissions/54410d1e-a1d1-4eae-a463-56994d510b34

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_gqM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_mem_good_set_or_weight_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sm_FM

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : ContinuousOn F (GV k r)) :
    (∫⁻ g, ‖FM F g‖ₑ ∂D.μG) = ∫⁻ q : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) * jc_E D F q := by
  have hf : Measurable fun x : Mt k r => ‖FM F x‖ₑ := (sm_FM hF).enorm
  rw [hI _ hf]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_good_set_or_weight_zero D] with q hq
  rcases hq with h | h
  · unfold jc_E
    rw [gqM_eq D h]
    rfl
  · rw [h]
    simp
end Formalism.FourierDecayAlt.P.B7
