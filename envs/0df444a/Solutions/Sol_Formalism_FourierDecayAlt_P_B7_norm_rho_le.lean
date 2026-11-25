-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.norm_rho_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:46:39.930212+00:00
-- url     : https://prove2.me/submissions/280a2201-7c39-4784-a146-8dd30a784f07

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_norm_pi_le
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B7_norm_pi__le_53d20754f3c3
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv


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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
attribute [local instance] sfG sfW sfN sfW'
attribute [local instance] sfSS
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (F : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : ‖rho D p F g‖ ≤ ‖F (sgs p g)‖ := by
  obtain ⟨h1, -, h3, -⟩ := hp
  unfold rho
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans ?_
  calc ‖D.π (Matrix.of p.1.1)‖ * (‖F (sgs p g)‖ * ‖D.π' (Matrix.of p.2.1)⁻¹‖)
      ≤ 1 * (‖F (sgs p g)‖ * 1) :=
        mul_le_mul (norm_pi_le D h1) (mul_le_mul_of_nonneg_left (norm_pi'_le D (WeylGroupFacts.uw_inv h3)) (norm_nonneg _))
          (by positivity) zero_le_one
    _ = ‖F (sgs p g)‖ := by ring
end Formalism.FourierDecayAlt.P.B7
