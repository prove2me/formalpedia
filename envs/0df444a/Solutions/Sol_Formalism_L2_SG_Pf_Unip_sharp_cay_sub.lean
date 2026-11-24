-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.sharp_cay_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:26:40.716913+00:00
-- url     : https://prove2.me/submissions/ffab462d-7cfb-41dc-9a6e-64eb40d1b2d4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_sharp
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_sub
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_one
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_cay_sub

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
variable {lv : ι → ℕ} {k : ℕ}
variable [StarRing K] [Invertible (2 : K)] {T : ℕ} {J J' : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (hJ : Graded lv T J) (hJ' : Graded lv T J') (h : J' * J = 1) (N : ℕ)
    {W : Matrix ι ι K} (hW : InPat lv k W) :
    InPat lv (k + k) (sharp J J' (cay (N + 1) W) - 1 - sharp J J' W) := by
  have e : sharp J J' (cay (N + 1) W) - 1 - sharp J J' W
      = sharp J J' (cay (N + 1) W - 1 - W) := by
    rw [sharp_sub, sharp_sub, sharp_one h]
  rw [e]
  exact inPat_sharp hJ hJ' (cay_sub N hW)
end Formalism.L2.SG.Pf.Unip
