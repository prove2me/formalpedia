-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.inPat_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:29.37578+00:00
-- url     : https://prove2.me/submissions/44f09e37-a88d-4bfb-9690-df713a4ae08d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_sub
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_smul
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_sharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
variable {lv : ι → ℕ} {T k : ℕ}
variable {J J' : Matrix ι ι K}
variable [Invertible (2 : K)]
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (hJ : Graded lv T J) (hJ' : Graded lv T J') {M : Matrix ι ι K} (hM : InPat lv k M) :
    InPat lv k (proj J J' M) := by
  unfold proj
  exact inPat_smul _ (inPat_sub hM (inPat_sharp hJ hJ' hM))
end Formalism.L2.SG.Pf.Unip
