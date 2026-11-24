-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.capelli_independence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:37.222882+00:00
-- url     : https://prove2.me/submissions/21af24b6-86af-4284-afc7-89c46181155a

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_sdec_shf
import Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_indep_char
import Theorems.Thm_Formalism_FourierDecayAlt_P_separating_polynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_Qr_mem_CapSp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.CapIndep := by
  intro V _ _ n E β
  refine indep_char (qdet E) (fun M : {M : Fin n → ℤ // StrictAnti M} => cpol (shf β M.1)) ?_ _
    (fun M v => mem_CapSp)
  intro M M' h
  have h1 := (separating_polynomials n (shf β M.1) (shf β M'.1) (fun w => congrFun h w) (sdec_shf β M'.2)).2
    (sdec_shf β M.2)
  apply Subtype.ext
  funext j
  have h2 := congrFun h1 j
  simp only [shf, add_right_inj] at h2
  exact_mod_cast h2
end Formalism.FourierDecayAlt.P
