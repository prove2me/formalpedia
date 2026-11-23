-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.act_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:02.752616+00:00
-- url     : https://prove2.me/submissions/158300dc-dff9-4ba4-9338-49aec701ba24

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities

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
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution (X : Ix S → V) : act (1 : SlopeTestRemainingChoices S A) X = X := by
  funext z; simp [act, Matrix.one_apply, ite_smul]
end Formalism.FourierDecayAlt.P.GramProductIdentities
