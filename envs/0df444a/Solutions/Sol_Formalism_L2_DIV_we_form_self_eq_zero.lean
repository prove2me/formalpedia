-- Prove2me | solution 1 for Formalism.L2.DIV.we_form_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:18.465669+00:00
-- url     : https://prove2.me/submissions/42a29997-e563-47c7-8c89-cab2e79bc270

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
import Theorems.Thm_Formalism_L2_DIV_we_hw_norm_ne
import Theorems.Thm_Formalism_L2_DIV_weForm_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.GradedWeylDivisibility
variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
namespace Formalism.L2.DIV
theorem _root_.solution (x : dualWeyl ℚ r n ν) (h : weForm hn ν x x = 0) : x = 0 := by
  rw [weForm_apply, div_eq_zero_iff] at h
  have h1 := h.resolve_right (we_hw_norm_ne hn ν)
  by_contra hx
  have hx' : x.1 ≠ 0 := fun h0 => hx (Subtype.ext h0)
  exact ne_of_gt ((fockQPos _ x.1 x.1).2 hx') h1
end Formalism.L2.DIV
