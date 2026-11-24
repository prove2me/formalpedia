-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.sharp_cay_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:26:41.460195+00:00
-- url     : https://prove2.me/submissions/84f8a202-0b65-480b-a8fd-d3c09aa55957

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_sharp
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_sub
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_one
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_cay_sub_one

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
    {W : Matrix ι ι K} (hW : InPat lv k W) : InPat lv k (sharp J J' (cay N W) - 1) := by
  have e : sharp J J' (cay N W) - 1 = sharp J J' (cay N W - 1) := by
    rw [sharp_sub, sharp_one h]
  rw [e]
  exact inPat_sharp hJ hJ' (cay_sub_one N hW)
end Formalism.L2.SG.Pf.Unip
