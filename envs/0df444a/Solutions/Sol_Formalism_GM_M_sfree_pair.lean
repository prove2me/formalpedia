-- Prove2me | solution 1 for Formalism.GM.M.sfree_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:32.982435+00:00
-- url     : https://prove2.me/submissions/199e814a-f1c7-4b07-9b19-586fc1f31611

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_SFree_sum
import Theorems.Thm_Formalism_GM_M_inl_ne_scalS

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
variable {t : ℕ}
namespace Formalism.GM.M
theorem _root_.solution (u w : Fin r → Fin (N + 1) × Fin r) :
    SFree (scalS N r t) (∑ c, X (Sum.inl (u c)) * X (Sum.inl (w c)) : MvPolynomial (BVar N r t) ℚ_[p]) :=
  SFree.sum _ _ _ (fun c _ => (SFree.X _ (inl_ne_scalS _)).mul _ (SFree.X _ (inl_ne_scalS _)))
end Formalism.GM.M
