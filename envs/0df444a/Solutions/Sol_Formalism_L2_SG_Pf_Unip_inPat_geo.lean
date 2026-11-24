-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.inPat_geo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:41:40.827834+00:00
-- url     : https://prove2.me/submissions/0ec41745-1787-4579-821d-ea555febabe9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_mono
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_pow
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_sum

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
theorem _root_.solution {Z : Matrix ι ι K} (hZ : InPat lv k Z) (N : ℕ) : InPat lv 0 (geo N Z) := by
  unfold geo
  exact inPat_sum fun j _ => inPat_mono (Nat.zero_le _) (inPat_pow hZ j)
end Formalism.L2.SG.Pf.Unip
