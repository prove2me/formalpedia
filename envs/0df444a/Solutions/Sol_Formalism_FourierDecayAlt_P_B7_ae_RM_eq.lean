-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.ae_RM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:39:38.371315+00:00
-- url     : https://prove2.me/submissions/988490db-b976-4333-b4c5-09b7105b1bc2

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_gq_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_gqM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_RM_eq

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D) :
    ∀ᵐ p ∂D.μSS, RM D F p (gqM D q) = rho D p F (gq D q) := by
  filter_upwards [ae_inSS D] with p hp
  rw [gqM_eq D hq]
  exact RM_eq D F hp (gq_mem D hq)
end Formalism.FourierDecayAlt.P.B7
