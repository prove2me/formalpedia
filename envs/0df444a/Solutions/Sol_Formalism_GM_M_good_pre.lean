-- Prove2me | solution 1 for Formalism.GM.M.good_pre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:07.633946+00:00
-- url     : https://prove2.me/submissions/9c7e7f66-ce14-479a-a3f0-6d3c2279e4e3

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_Good_pow
import Theorems.Thm_Formalism_GM_M_SSD_Good_prod
import Theorems.Thm_Formalism_GM_M_SSD_SFree_prod
import Theorems.Thm_Formalism_GM_M_SSD_SFree_pow
import Theorems.Thm_Formalism_GM_M_good_tie
import Theorems.Thm_Formalism_GM_M_sfree_pair

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
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) :
    ∃ s, Good (scalS N r D.T.t) (pre (p := p) (r := r) D j jp) (lv j jp) s := by
  have hE : ∀ i, Good (scalS N r D.T.t) (D.Ehat p (r := r) i) (Pi.single (Fin.castSucc i) 1) _ :=
    fun i => good_tie (Fin.castSucc i) _ (sfree_pair _ _)
  have hP : Good (scalS N r D.T.t) (D.Eplus p (r := r)) (Pi.single (Fin.last D.T.t) 1) _ :=
    good_tie (Fin.last D.T.t) _ (sfree_pair _ _)
  exact ⟨_, (Good.prod _ univ (fun i => D.Ehat p (r := r) i ^ j i) _ _ (fun i _ => (hE i).pow _ (j i))).mul _
    (hP.pow _ jp)⟩
end Formalism.GM.M
