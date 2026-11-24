-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.inner_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:55:15.213995+00:00
-- url     : https://prove2.me/submissions/808360df-7e88-4b2a-8e9f-b8ee207cd22c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_al_hs_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_al_rho_tr
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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {p' p : SS k r} (hp' : D.inSS p')
    (hp : D.inSS p) (g : Mat k r) :
    inner ℂ (hsVec (rho D p' F g)) (hsVec (rho D (tr p' p) F g)) =
      hsInner (rho D p F (sgs p' g)) (F (sgs p' g)) := by
  have e : rho D p' F g = (D.π (Matrix.of p'.1.1)).comp ((F (sgs p' g)).comp (D.π' (Matrix.of p'.2.1)⁻¹)) := rfl
  rw [e, al_rho_tr D F hp' hp g]
  exact al_hs_inv _ (D.π_unitary _ hp'.1) _ (D.π'_unitary _ (WeylGroupFacts.uw_inv hp'.2.2.1)) _ _
end Formalism.FourierDecayAlt.P.B7
