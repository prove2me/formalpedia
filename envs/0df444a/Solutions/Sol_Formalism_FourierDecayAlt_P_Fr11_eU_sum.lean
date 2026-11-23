-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.eU_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:08.936528+00:00
-- url     : https://prove2.me/submissions/2bb962a3-db05-4e53-a0ce-b992f3f3f7f7

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_eU_same

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (a : S) : (eU a 0 0 + eU a 1 1 : SlopeTestRemainingChoices S A) = 1 := by
  rw [eU_same, eU_same, dg_add, ← dg_one]
  congr 1
  funext e
  generalize e a = k
  fin_cases k <;> simp
end Formalism.FourierDecayAlt.P.Fr11
