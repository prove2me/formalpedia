-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.pair_act
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:23.654057+00:00
-- url     : https://prove2.me/submissions/53a72492-7a6c-4f48-ab60-a4d7b0f92c07

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
theorem _root_.solution (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X X' : Ix S → V) :
    pair ρ (act M X) X' = pair ρ X (act (star M) X') := by
  simp only [pair, act, map_sum, LinearMap.sum_apply, ρ.adj, Matrix.star_apply]
  exact Finset.sum_comm
end Formalism.FourierDecayAlt.P.GramProductIdentities
