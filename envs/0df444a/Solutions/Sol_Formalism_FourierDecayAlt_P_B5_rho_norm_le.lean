-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.rho_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:06:04.400442+00:00
-- url     : https://prove2.me/submissions/522ef4ac-612c-4070-9047-c95032cdba84

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (F : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : ‖rho D p F g‖ ≤ ‖F (sgs p g)‖ := by
  unfold RealPlaceData.inSS at hp
  have h1 := hp.1
  have h3 := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1
  unfold rho
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [ContinuousLinearMap.comp_apply, D.π_unitary _ h1, ContinuousLinearMap.comp_apply]
  calc ‖F (sgs p g) (D.π' (Matrix.of p.2.1)⁻¹ v)‖ ≤ ‖F (sgs p g)‖ * ‖D.π' (Matrix.of p.2.1)⁻¹ v‖ :=
        (F (sgs p g)).le_opNorm _
    _ = ‖F (sgs p g)‖ * ‖v‖ := by rw [D.π'_unitary _ h3]
end Formalism.FourierDecayAlt.P.B5
