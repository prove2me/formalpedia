-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.fock_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:52:58.756906+00:00
-- url     : https://prove2.me/submissions/1174ec8f-51a5-40a1-b3a4-278454ca40a0

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_comm
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_add_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (F G G' : MvPolynomial σ ℚ_[p]) :
    M.fock p F (G + G') = M.fock p F G + M.fock p F G' := by
  rw [fock_comm p F (G + G'), fock_add_left, fock_comm p G F, fock_comm p G' F]
end Formalism.GM.GammaExpansion
