-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.xi_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:54.244227+00:00
-- url     : https://prove2.me/submissions/c68ef8f0-ed93-4ec0-b735-afedcc779815

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_al_lam_tr

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) {p' p : SS k r} (hp' : D.inSS p') (hp : D.inSS p) :
    xiTau D τ (tr p' p) = xiTau D τ p' * xiTau D τ p := by
  obtain ⟨a1, a2, a3, a4⟩ := hp'
  obtain ⟨b1, b2, b3, b4⟩ := hp
  have e1 : lam k r D.z (Matrix.of (tr p' p).1.2) = lam k r D.z (Matrix.of p'.1.2) + lam k r D.z (Matrix.of p.1.2) :=
    al_lam_tr D.z D.z_mem a1 a2 b2
  have e2 : lam k r D.z' (Matrix.of (tr p' p).2.2) = lam k r D.z' (Matrix.of p'.2.2) + lam k r D.z' (Matrix.of p.2.2) :=
    al_lam_tr D.z' D.z'_mem a3 a4 b4
  unfold xiTau
  rw [e1, e2, ← Complex.exp_add]
  congr 1
  push_cast
  ring
end Formalism.FourierDecayAlt.P.B7
