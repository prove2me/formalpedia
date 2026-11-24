-- Prove2me | solution 1 for Formalism.GM.M.Q_of_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:44:49.217356+00:00
-- url     : https://prove2.me/submissions/9bdf592d-e046-42fd-b065-9d45c77d27b3

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_sfree_span
import Theorems.Thm_Formalism_GM_M_topV

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
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hv : v ∈ Submodule.span ℚ_[p] (D.gens p (r := r) j jp)) (P : ℚ_[p] → Prop) (hP0 : P 0)
    (htop : ∀ m, sd (scalS N r D.T.t) m = lv j jp → P (coeff m v)) :
    ∃ Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp), v = pre D j jp * Q ∧ ∀ n, P (coeff n Q) := by
  obtain ⟨s, Q, hQ, hvQ, hs, _, hc⟩ := topV D j jp v hv
  refine ⟨Q, hQ, hvQ, fun n => ?_⟩
  by_cases hn : n ∈ Q.support
  · rw [← hc n]; apply htop; rw [sd_add, hs, sfree_span D j jp Q hQ n hn, add_zero]
  · rw [notMem_support_iff.mp hn]; exact hP0
end Formalism.GM.M
