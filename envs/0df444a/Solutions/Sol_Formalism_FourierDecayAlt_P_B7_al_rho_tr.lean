-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.al_rho_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:29:31.095725+00:00
-- url     : https://prove2.me/submissions/efa3ea67-3b0d-4921-bcd0-f80f40822502

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_al_sgs_tr
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
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
    rho D (tr p' p) F g = (D.π (Matrix.of p'.1.1)).comp
      ((rho D p F (sgs p' g)).comp (D.π' (Matrix.of p'.2.1)⁻¹)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  obtain ⟨g1, g2, g3, g4⟩ := hp
  have e0 := al_sgs_tr (p := p) (WeylGroupFacts.isUnit_of_uh h1.1) (WeylGroupFacts.isUnit_of_uh h3.1) g
  have e1 : D.π (Matrix.of (tr p' p).1.1) = (D.π (Matrix.of p'.1.1)).comp (D.π (Matrix.of p.1.1)) :=
    D.π_rep.2 _ h1 _ g1
  have e2 : D.π' (Matrix.of (tr p' p).2.1)⁻¹ = (D.π' (Matrix.of p.2.1)⁻¹).comp (D.π' (Matrix.of p'.2.1)⁻¹) := by
    have : ((Matrix.of (tr p' p).2.1 : Mat k r))⁻¹ = (Matrix.of p.2.1)⁻¹ * (Matrix.of p'.2.1)⁻¹ :=
      Matrix.mul_inv_rev _ _
    rw [this]
    exact D.π'_rep.2 _ (WeylGroupFacts.uw_inv g3) _ (WeylGroupFacts.uw_inv h3)
  unfold rho
  rw [e0, e1, e2]
  rfl
end Formalism.FourierDecayAlt.P.B7
