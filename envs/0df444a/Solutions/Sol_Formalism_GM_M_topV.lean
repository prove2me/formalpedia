-- Prove2me | solution 1 for Formalism.GM.M.topV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:28.090411+00:00
-- url     : https://prove2.me/submissions/880f1088-55a0-4d9a-908a-8d47cbfa9169

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_Good_mul_sfree
import Theorems.Thm_Formalism_GM_M_good_pre
import Theorems.Thm_Formalism_GM_M_memV
import Theorems.Thm_Formalism_GM_M_sfree_span

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
    (hv : v ∈ Submodule.span ℚ_[p] (D.gens p (r := r) j jp)) :
    ∃ s Q, Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp) ∧ v = pre D j jp * Q ∧
      sd (scalS N r D.T.t) s = lv j jp ∧ (∀ m ∈ v.support, sd (scalS N r D.T.t) m ≤ lv j jp) ∧
      ∀ n, coeff (s + n) v = coeff n Q := by
  obtain ⟨Q, hQ, rfl⟩ := memV D j jp v hv
  obtain ⟨s, hs⟩ := good_pre (p := p) (r := r) D j jp
  obtain ⟨h1, h2⟩ := hs.mul_sfree _ (sfree_span D j jp Q hQ)
  exact ⟨s, Q, hQ, rfl, hs.1, h1, h2⟩
end Formalism.GM.M
