-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.fock_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:58.273513+00:00
-- url     : https://prove2.me/submissions/a45d1082-6bbb-4e8d-81a8-5505a0e4cd7d

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_eq_sum

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
theorem _root_.solution (F G : MvPolynomial σ ℚ_[p]) : M.fock p F G = M.fock p G F := by
  rw [fock_eq_sum p F G (F.support ∪ G.support) (fun x hx => Finset.mem_union_left _ hx),
    fock_eq_sum p G F (F.support ∪ G.support) (fun x hx => Finset.mem_union_right _ hx)]
  exact Finset.sum_congr rfl fun m _ => by ring
end Formalism.GM.GammaExpansion
