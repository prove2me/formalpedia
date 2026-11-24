-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.EH_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:57:18.735203+00:00
-- url     : https://prove2.me/submissions/1ed55136-7080-437a-8a00-042a250e78a3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_dx_repF
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xa_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xb_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) (a b : Fin (2 * r + k + 1)) :
    Q.EH k r a b φ g = Psi F' g (Matrix.single a b 1) := by
  have h1 : RdV (Xa k r a b) φ g = F' (g * Xa k r a b) := dx_repF (Xa_lie a b) hU hgU hg hF hff
  have h2 : RdV (Xb k r a b) φ g = F' (g * Xb k r a b) := dx_repF (Xb_lie a b) hU hgU hg hF hff
  show RdV (Xa k r a b) φ g + Complex.I • RdV (Xb k r a b) φ g =
    F' (g * Xa k r a b) + Complex.I • F' (g * Xb k r a b)
  rw [h1, h2]
end Formalism.FourierDecayAlt.P.JFxE
