-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.cay_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:00:09.833631+00:00
-- url     : https://prove2.me/submissions/a29150af-eb49-48cb-89ea-505e8247a5a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_smul
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_mul
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_geo

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
theorem _root_.solution (N : ℕ) {Z : Matrix ι ι K} (hZ : InPat lv k Z) : InPat lv k (cay N Z - 1) := by
  unfold cay
  rw [add_sub_cancel_left]
  have := inPat_mul hZ (inPat_geo (inPat_smul (⅟2 : K) hZ) N)
  rwa [Nat.add_zero] at this
end Formalism.L2.SG.Pf.Unip
