-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cT_diff2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:20:44.956808+00:00
-- url     : https://prove2.me/submissions/04a2283f-0469-4a1d-94d0-06b5a4725f8a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_charSum_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_abel_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_lw_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_lw_anti
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cT_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (hχ : χ ≠ 1) (U V : ℕ) (hU : 2 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 2 * ((q : ℝ) + 1) * lw (U + 1) := by
  rw [cT_sub χ U V hUV]
  exact abel_bound (fun n => χ (n : ZMod q)) lw _ (charSum_le χ hχ) U V hUV (lw_nonneg _)
    (fun n hn => lw_anti n (by omega))
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
