-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.cay_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:05:21.875515+00:00
-- url     : https://prove2.me/submissions/a49e671c-cb1c-4e8a-b5bf-f831e23fc407

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_smul
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_mul
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_geo
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_geo_succ

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]
variable {lv : ι → ℕ} {k : ℕ}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (N : ℕ) {Z : Matrix ι ι K} (hZ : InPat lv k Z) : InPat lv (k + k) (cay (N + 1) Z - 1 - Z) := by
  unfold cay
  rw [geo_succ, add_sub_cancel_left, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_right]
  have := inPat_mul hZ (inPat_mul (inPat_smul (⅟2 : K) hZ)
    (inPat_geo (inPat_smul (⅟2 : K) hZ) N))
  rwa [Nat.add_zero] at this
end Formalism.L2.SG.Pf.Unip
