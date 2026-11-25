-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.La_AAx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:09.94744+00:00
-- url     : https://prove2.me/submissions/cdeac2f5-8eb6-4ee2-adc7-32272348779d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_AAop_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_raising_operator_level_zero

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
theorem _root_.solution (hD : IsOpen D) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D) (m : ℕ) (hm : m ≤ r) (u : ℂ) :
    La hD K hK x₁ (C3.AAx k r (E0 hD) (xi0 x₁) m hm u) = C3.AAop k r m hm u K x₁ := by
  show (((C3.AAx k r (E0 hD) (xi0 x₁) m hm u) (vK hD K hK)) : Q.Mx k r → E) x₁ = _
  rw [← raising_operator_level_zero hD m hm u (vK hD K hK) x₁ hx₁]
  exact AAop_loc hD m hm u _ K (fun x hx => cut_of_mem K hx) x₁ hx₁
end Formalism.FourierDecayAlt.P.PBG
