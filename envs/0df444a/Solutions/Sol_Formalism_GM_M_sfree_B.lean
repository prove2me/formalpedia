-- Prove2me | solution 1 for Formalism.GM.M.sfree_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:48.01388+00:00
-- url     : https://prove2.me/submissions/696d69a8-03d8-4f63-9746-11bddad62661

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_Good_pow
import Theorems.Thm_Formalism_GM_M_SSD_Good_prod
import Theorems.Thm_Formalism_GM_M_SSD_SFree_prod
import Theorems.Thm_Formalism_GM_M_SSD_SFree_pow
import Theorems.Thm_Formalism_GM_M_scalZ_ne_scalS
import Theorems.Thm_Formalism_GM_M_zmon_eq
import Theorems.Thm_Formalism_GM_M_sfree_xi

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
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ Bset (p := p) D j jp) : SFree (scalS N r D.T.t) x := by
  obtain ⟨y, _, g, hg, rfl⟩ := hx
  refine (SFree.mul _ (SFree.mul _ ?_ ?_) (sfree_xi D hg))
  · rw [← zmon_eq]
    exact SFree.mul _ (SFree.prod _ _ _ fun i _ => (SFree.X _ (scalZ_ne_scalS _)).pow _ _)
      ((SFree.X _ (scalZ_ne_scalS _)).pow _ _)
  · exact SFree.rename _ _ (fun x k => by simp [chainEmb, scalS]) y
end Formalism.GM.M
