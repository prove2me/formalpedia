-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SandwichRhoAction.sandw_leftInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:45:17.495009+00:00
-- url     : https://prove2.me/submissions/a8582a09-1dab-4f5f-a39c-5f3fcbff7aad

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_sandw_apply
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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SandwichRhoAction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SandwichRhoAction
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (A : Wq →L[ℂ] Wp) :
    sandw (D.π (Matrix.of p.1.1)⁻¹) (D.π' (Matrix.of p.2.1))
      (sandw (D.π (Matrix.of p.1.1)) (D.π' (Matrix.of p.2.1)⁻¹) A) = A := by
  have h1 := hp.1
  have h3 := hp.2.2.1
  have u1 := WeylGroupFacts.isUnit_of_uh h1.1
  have u3 := WeylGroupFacts.isUnit_of_uh h3.1
  have e1 : (D.π (Matrix.of p.1.1)⁻¹).comp (D.π (Matrix.of p.1.1)) = 1 := by
    rw [← D.π_rep.2 _ (WeylGroupFacts.uw_inv h1) _ h1, Matrix.nonsing_inv_mul _ u1, D.π_rep.1]
  have e3 : (D.π' (Matrix.of p.2.1)⁻¹).comp (D.π' (Matrix.of p.2.1)) = 1 := by
    rw [← D.π'_rep.2 _ (WeylGroupFacts.uw_inv h3) _ h3, Matrix.nonsing_inv_mul _ u3, D.π'_rep.1]
  have re : ∀ (P1 P2 : Wp →L[ℂ] Wp) (Q1 Q2 : Wq →L[ℂ] Wq) (B : Wq →L[ℂ] Wp),
      P1.comp ((P2.comp (B.comp Q2)).comp Q1) = (P1.comp P2).comp (B.comp (Q2.comp Q1)) := by
    intros; ext; rfl
  simp only [sandw_apply]
  rw [re, e1, e3]
  ext; rfl
end Formalism.FourierDecayAlt.P.SandwichRhoAction
