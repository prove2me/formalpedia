-- Prove2me | solution 1 for Formalism.GM.M.Ehat_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:09.268199+00:00
-- url     : https://prove2.me/submissions/1c6f9d8b-ced0-4f5c-8a0b-0d00b7ca4c54

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_P2M_Formalism_GM_M_intPol_mul__5d0d8163dde2
import Theorems.Thm_P2M_Formalism_GM_M_intPol_X__68061b67f887

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (D : BlockData N)
namespace Formalism.GM.M
theorem _root_.solution (i : Fin D.T.t) : D.Ehat p (r := r) i ∈ IntPol p (BVar N r D.T.t) := by
  unfold BlockData.Ehat
  exact Submodule.add_mem _ (intPol_mul' (intPol_X' _) (intPol_X' _))
    (Submodule.sum_mem _ fun c _ => intPol_mul' (intPol_X' _) (intPol_X' _))
end Formalism.GM.M
