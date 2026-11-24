-- Prove2me | solution 1 for Formalism.GM.M.sfree_xi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:03.453971+00:00
-- url     : https://prove2.me/submissions/12be8d32-0e02-4c63-9e87-c3e093191006

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_xi_mono

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
theorem _root_.solution {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b) :
    SFree (scalS N r D.T.t) g := by
  intro m hm; funext k; simp only [sd, Pi.zero_apply]
  by_contra h
  obtain ⟨c, hc⟩ := (xi_mono D hg hm).1 _ (Finsupp.mem_support_iff.mpr h)
  simp [scalS, xiVar] at hc
end Formalism.GM.M
