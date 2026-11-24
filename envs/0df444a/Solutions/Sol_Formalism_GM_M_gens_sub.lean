-- Prove2me | solution 1 for Formalism.GM.M.gens_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:02.213902+00:00
-- url     : https://prove2.me/submissions/39efd758-918a-4317-b3bc-46a6908136f4

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_zmon_eq

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
    (hx : x ∈ D.gens p (r := r) j jp) : ∃ b ∈ Bset (p := p) D j jp, x = pre D j jp * b := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  refine ⟨_, ⟨y, hy, g, hg, rfl⟩, ?_⟩
  rw [pre, ← zmon_eq]; ring
end Formalism.GM.M
