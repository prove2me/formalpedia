-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.w_hk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:19.690049+00:00
-- url     : https://prove2.me/submissions/6dc7ebd0-303f-4060-9c7b-6f691e9251c4

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sgs_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_gq_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_inner_tr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_KM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_Phi_eq

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D)
    (p p' : SS k r) (hp : D.inSS p) (hp' : D.inSS p') :
    inner ℂ (hsVec (rho D p F (gq D q))) (hsVec (rho D (tr p p') F (gq D q))) = KM D F p' (PhiM D (q, p)) := by
  have hx : Matrix.of (PhiM D (q, p)) ∈ GV k r := by
    rw [w_Phi_eq D hq]
    exact sgs_mem D hp (gq_mem D hq)
  rw [inner_tr D F hp hp' (gq D q), u_KM_eq D F hp' hx, w_Phi_eq D hq]
  all_goals rfl
end Formalism.FourierDecayAlt.P.B7
