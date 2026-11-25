-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.u_enorm_KM_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:06:11.23166+00:00
-- url     : https://prove2.me/submissions/810c56e4-4247-4347-9fd5-6157c85de34a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_norm_rho_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_KM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_norm_hsInner_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_sgs_eq

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : D.inSS p)
    {x : Mt k r} (hx : Matrix.of x ∈ GV k r) :
    ‖KM D F p x‖ₑ ≤ ENNReal.ofReal (‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2) *
      (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of x * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
        ‖F (Matrix.of x)‖ₑ) := by
  rw [u_KM_eq D F hp hx, ← u_sgs_eq, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ((u_norm_hsInner_le _ _).trans ?_)
  have := norm_rho_le D hp F (Matrix.of x)
  gcongr
end Formalism.FourierDecayAlt.P.B7
