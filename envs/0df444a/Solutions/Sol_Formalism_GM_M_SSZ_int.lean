-- Prove2me | solution 1 for Formalism.GM.M.SSZ_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:57.775286+00:00
-- url     : https://prove2.me/submissions/47cfa5c6-9690-41aa-9c8f-440578c54ebd

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_P2M_Formalism_GM_M_intPol_mul__5d0d8163dde2
import Theorems.Thm_P2M_Formalism_GM_M_intPol_X__68061b67f887
import Theorems.Thm_P2M_Formalism_GM_M_intPol_pow__7258d14ed956
import Theorems.Thm_P2M_Formalism_GM_M_intPol_prod__f889d80e71c9
import Theorems.Thm_P2M_Formalism_GM_M_intPol_rename__d2058bf01e91
import Theorems.Thm_Formalism_GM_M_Ehat_int
import Theorems.Thm_Formalism_GM_M_Eplus_int

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
theorem _root_.solution (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hx : x ∈ D.SSZ p (r := r)) :
    x ∈ IntPol p (BVar N r D.T.t) := by
  refine (Submodule.span_le.mpr ?_) hx
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, _, y, hy, g, hg, rfl⟩ := hx
  have hyI : y ∈ IntPol p (Fin N × Fin r) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).2).2
  have hgI : g ∈ IntPol p (BVar N r D.T.t) := (Submodule.mem_inf.mp hg).2
  refine intPol_mul' (intPol_mul' (intPol_mul' (intPol_mul' (intPol_mul' ?_ ?_) ?_) ?_)
    (intPol_rename' _ hyI)) hgI
  · exact intPol_prod' _ _ fun i _ => intPol_pow' (Ehat_int D i) _
  · exact intPol_pow' (Eplus_int D) _
  · exact intPol_prod' _ _ fun i _ => intPol_pow' (intPol_X' _) _
  · exact intPol_pow' (intPol_X' _) _
end Formalism.GM.M
