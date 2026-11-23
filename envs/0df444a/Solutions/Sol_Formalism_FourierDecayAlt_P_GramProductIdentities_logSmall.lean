-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.logSmall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:49.131782+00:00
-- url     : https://prove2.me/submissions/c32eb307-e4f3-4f82-b685-a1d67db68aee

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_exp_le_one_add

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
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution : LogSmall := by
  intro x hx
  have hpos : 0 < 1 + x := by
    have := neg_abs_le x; linarith
  rw [abs_le]
  constructor
  · have h := exp_le_one_add hx
    have := Real.log_le_log (Real.exp_pos _) h
    rw [Real.log_exp] at this
    linarith
  · have := Real.log_le_sub_one_of_pos hpos
    have := le_abs_self x
    have := abs_nonneg x
    linarith
end Formalism.FourierDecayAlt.P.GramProductIdentities
