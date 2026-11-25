-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.La_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:49:35.594267+00:00
-- url     : https://prove2.me/submissions/774c7c31-9956-4a0c-b1de-6f2eb6a04c58

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_level_zero_derivative_rule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g)
    (x₁ : Q.Mx k r) : C3.RightRuleFn k r z' (E0 hD) (La hD K hK x₁) := by
  intro X p q hpq
  show (((X * E0 hD p q : Module.End ℂ (VS k r 0 D E)) (vK hD K hK)) : Q.Mx k r → E) x₁ = C3.dpsiP k r z' p q • ((X (vK hD K hK)) : Q.Mx k r → E) x₁
  rw [Module.End.mul_apply, level_zero_derivative_rule hD z' K hK hR p q hpq, map_smul]
  rfl
end Formalism.FourierDecayAlt.P.PBG
