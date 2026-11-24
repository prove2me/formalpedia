-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.fock_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:52.213212+00:00
-- url     : https://prove2.me/submissions/13b83578-9e33-4378-a8b3-cb29331d86a4

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_comm
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_smul_left

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
theorem _root_.solution (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) :
    M.fock p F (c • G) = c * M.fock p F G := by
  rw [fock_comm p F (c • G), fock_smul_left, fock_comm p G F]
end Formalism.GM.GammaExpansion
