-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BesselScaling.lemmaBFromXi_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:59:16.759925+00:00
-- url     : https://prove2.me/submissions/0324ac42-6558-48a4-a0e1-863e0de5842f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselScaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_lemma_b_from_xi_of_parts
import Theorems.Thm_Formalism_FourierDecayAlt_P_adjointness_polynomially_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_lemma_closed_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_clause_of_regularized_limit
import Theorems.Thm_Formalism_FourierDecayAlt_P_lemma_B_of_components


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BesselScaling
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.BesselScaling
theorem _root_.solution : ConjInvAll → DilJacAll → CCIntAll → IntNormB → LemmaBFromXi :=
  Formalism.FourierDecayAlt.P.lemma_b_from_xi_of_parts (fun hX => Formalism.FourierDecayAlt.P.bessel_lemma_closed_form hX Formalism.FourierDecayAlt.P.lemma_B_of_components
            Formalism.FourierDecayAlt.P.clause_of_regularized_limit Formalism.FourierDecayAlt.P.adjointness_polynomially_bounded)
end Formalism.FourierDecayAlt.P.BesselScaling
