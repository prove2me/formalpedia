-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.cs_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:15.655822+00:00
-- url     : https://prove2.me/submissions/d575d456-500e-4dce-b721-14f1e988c9e5

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Bl_HermitianSesquilinear_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution (Ξ : F7.Sesq M) (h : ∀ m, 0 ≤ (Ξ m m).re ∧ (Ξ m m).im = 0) (x y : M) :
    ‖Ξ x y‖ ^ 2 ≤ (Ξ x x).re * (Ξ y y).re := by
  first | exact Bl.HermitianSesquilinear.goal1 .. | (apply Bl.HermitianSesquilinear.goal1 <;> assumption) | (intros; apply Bl.HermitianSesquilinear.goal1 <;> assumption) | (apply @Bl.HermitianSesquilinear.goal1 <;> assumption) | (intros; apply @Bl.HermitianSesquilinear.goal1 <;> assumption) | (apply @Bl.HermitianSesquilinear.goal1 <;> first | assumption | infer_instance) | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h x y | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h x | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› | exact @Bl.HermitianSesquilinear.goal1 M ‹_› | exact @Bl.HermitianSesquilinear.goal1 M
end Formalism.FourierDecayAlt.P.GramProductIdentities
